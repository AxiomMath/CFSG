module

public import CFSG.Quasithin.H13.L32A712
public import CFSG.Quasithin.H13.L32A73

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

namespace L32A

variable {G : Type} [Group G]

theorem conj_mem_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ ⁅H, K⁆) : g * x * g⁻¹ ∈ ⁅H, K⁆ := by
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [Subgroup.map_commutator] at h1
  have eH : H.map (MulAut.conj g).toMonoidHom = H := conjSub_eq_self_iff.mpr hH
  have eK : K.map (MulAut.conj g).toMonoidHom = K := conjSub_eq_self_iff.mpr hK
  rw [eH, eK] at h1
  simpa [MulAut.conj_apply] using h1

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [← conjSub_eq_self_iff]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_commutator hH hK hx
  · intro x hx
    have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem hH
    have hK' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hK
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, conj_mem_commutator hg' hK' hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_of_forall_conj {Q R : Subgroup G}
    (h : ∀ q ∈ Q, ∀ x ∈ R, q * x * q⁻¹ ∈ R) {g : G} (hg : g ∈ Q) :
    g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem commutatorElement_mul_left' (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_conjClosure_eq {U L Q : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQU : Q ≤ Subgroup.normalizer (U : Set G))
    (hSQ : conjClosure U L ≤ Q) :
    ⁅conjClosure U L, Q⁆ = conjClosure ⁅U, Q⁆ L := by
  have hkey : ∀ q ∈ Q, ∀ x ∈ conjClosure ⁅U, Q⁆ L, q * x * q⁻¹ ∈ conjClosure ⁅U, Q⁆ L := by
    intro q hq x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, y, hy, rfl⟩ := hx
      have hq' : l⁻¹ * q * l ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hLQ (inv_mem hl)) q).mp hq
        simpa using this
      have hy' := conj_mem_commutator (hQU hq') (Subgroup.le_normalizer hq') hy
      have e : q * (l * y * l⁻¹) * q⁻¹ = l * ((l⁻¹ * q * l) * y * (l⁻¹ * q * l)⁻¹) * l⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure hl hy'
    | one => simp
    | mul x y _ _ hx hy =>
      have e : q * (x * y) * q⁻¹ = (q * x * q⁻¹) * (q * y * q⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  have hQR : Q ≤ Subgroup.normalizer ((conjClosure ⁅U, Q⁆ L : Subgroup G) : Set G) :=
    fun q hq => mem_normalizer_of_forall_conj hkey hq
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro s hs q hq
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, u, hu, rfl⟩ := hx
      have hq' : l⁻¹ * q * l ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hLQ (inv_mem hl)) q).mp hq
        simpa using this
      have e : ⁅l * u * l⁻¹, q⁆ = l * ⁅u, l⁻¹ * q * l⁆ * l⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mem_conjClosure hl (Subgroup.commutator_mem_commutator hu hq')
    | one => simp
    | mul x y hx _ ihx ihy =>
      rw [commutatorElement_mul_left']
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hQR (hSQ hx)) _).mp ihy) ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, q⁆ = x⁻¹ * ⁅x, q⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      rw [e]
      have h1 := (Subgroup.mem_normalizer_iff.mp (hQR (hSQ (inv_mem hx))) _).mp (inv_mem ihx)
      simpa using h1
  · refine conjClosure_le fun l hl x hx => ?_
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj l).toMonoidHom hx
    rw [Subgroup.map_commutator] at h1
    have eQ : Q.map (MulAut.conj l).toMonoidHom = Q := conjSub_eq_self_iff.mpr (hLQ hl)
    rw [eQ] at h1
    have hle : U.map (MulAut.conj l).toMonoidHom ≤ conjClosure U L := by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_conjClosure hl hu
    have := Subgroup.commutator_mono hle le_rfl h1
    simpa [MulAut.conj_apply] using this

theorem map_subtype_commutator_eq (H : Subgroup G) :
    (_root_.commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem commutator_closure_le {X : Set G} {B : Subgroup G}
    (hXB : ∀ x ∈ X, x ∈ Subgroup.normalizer (B : Set G))
    (hX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ B) :
    ⁅Subgroup.closure X, Subgroup.closure X⁆ ≤ B := by
  have hN : Subgroup.closure X ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.closure_le _).mpr hXB
  have hconj : ∀ g ∈ Subgroup.closure X, ∀ b ∈ B, g * b * g⁻¹ ∈ B := fun g hg b hb =>
    (Subgroup.mem_normalizer_iff.mp (hN hg) b).mp hb
  have step1 : ∀ s ∈ Subgroup.closure X, ∀ y ∈ X, ⁅s, y⁆ ∈ B := by
    intro s hs y hy
    induction hs using Subgroup.closure_induction with
    | mem x hx => exact hX x hx y hy
    | one => simp
    | mul a b ha _ iha ihb =>
      rw [commutatorElement_mul_left']
      exact mul_mem (hconj a ha _ ihb) iha
    | inv a ha iha =>
      have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj _ (inv_mem ha) _ (inv_mem iha)
  rw [Subgroup.commutator_le]
  intro s hs t ht
  induction ht using Subgroup.closure_induction with
  | mem y hy => exact step1 s hs y hy
  | one => simp
  | mul b c hb _ ihb ihc =>
    have e : ⁅s, b * c⁆ = ⁅s, b⁆ * (b * ⁅s, c⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ihb (hconj b hb _ ihc)
  | inv b hb ihb =>
    have e : ⁅s, b⁻¹⁆ = b⁻¹ * ⁅s, b⁆⁻¹ * b⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj _ (inv_mem hb) _ (inv_mem ihb)

theorem mem_normalizer_conjClosure {A L : Subgroup G} {g : G}
    (h : ∀ l ∈ L, g ∈ Subgroup.normalizer (conjSub l A : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure A L : Set G) := by
  have key : ∀ g : G, (∀ l ∈ L, g ∈ Subgroup.normalizer (conjSub l A : Set G)) →
      ∀ x ∈ conjClosure A L, g * x * g⁻¹ ∈ conjClosure A L := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, a, ha, rfl⟩ := hx
      have h1 : l * a * l⁻¹ ∈ conjSub l A := mul_mem_conjSub ha
      have h2 := (Subgroup.mem_normalizer_iff.mp (hg l hl) _).mp h1
      rw [mem_conjSub] at h2
      have e : g * (l * a * l⁻¹) * g⁻¹ =
          l * (l⁻¹ * (g * (l * a * l⁻¹) * g⁻¹) * l) * l⁻¹ := by group
      rw [e]
      exact mem_conjClosure hl h2
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g h x, fun hx => ?_⟩
  have := key g⁻¹ (fun l hl => inv_mem (h l hl)) _ hx
  simpa [mul_assoc] using this

theorem conjSub_le_normalizer {X Y : Subgroup G} (h : X ≤ Subgroup.normalizer (Y : Set G))
    (g : G) : conjSub g X ≤ Subgroup.normalizer (conjSub g Y : Set G) := by
  intro x hx
  rw [mem_conjSub] at hx
  have h1 := h hx
  rw [← conjSub_eq_self_iff] at h1 ⊢
  rw [← conjSub_mul, show x * g = g * (g⁻¹ * x * g) by group, conjSub_mul, h1]

theorem frattiniOf_eq_commutator [Finite G] {P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hsq : ∀ x ∈ P, x ^ 2 ∈ ⁅P, P⁆) : frattiniOf P = ⁅P, P⁆ := by
  apply le_antisymm
  · refine frattiniOf_le_of_forall (fun x hx y hy => ?_) hsq
    have := Subgroup.commutator_mem_commutator hx hy
    rwa [commutatorElement_def] at this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : ⁅(⟨a, ha⟩ : ↥P), (⟨b, hb⟩ : ↥P)⁆ ∈ frattini ↥P :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact ⟨_, h1, map_commutatorElement P.subtype ⟨a, ha⟩ ⟨b, hb⟩⟩

theorem sq_mem_commutator_closure {X : Set G} (hX : ∀ x ∈ X, x ^ 2 = 1) {x : G}
    (hx : x ∈ Subgroup.closure X) :
    x ^ 2 ∈ ⁅Subgroup.closure X, Subgroup.closure X⁆ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => rw [hX x hx]; exact one_mem _
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
      simp only [pow_two, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem iha (Subgroup.commutator_mem_commutator (inv_mem ha) hb)) ihb
  | inv a _ iha =>
    rw [inv_pow]
    exact inv_mem iha

theorem le_normalizer_pCoreOf_sup (T L : Subgroup G) :
    L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
  le_sup_left.trans (le_normalizer_pCoreOf 2 (L ⊔ T))

section Setting

variable [Finite G] {T L V : Subgroup G}

theorem fsuU_eq_conjClosure_hz (hMod : StmtL32NModule) (h : Hyp147 G T L V) :
    fsuU T V = conjClosure V (L32A.hz T V) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  show conjClosure V (Subgroup.normalizer (fsuV1 T V : Set G)) = _
  rw [normalizer_eq_centralizer_of_card_two hV1]

theorem sL_le_pCoreOf (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (hMod : StmtL32NModule) :
    L32A.sL T L V ≤ pCoreOf 2 (L ⊔ T) := by
  show conjClosure (fsuU T V) L ≤ _
  rw [fsuU_eq_conjClosure_hz hMod S.hyp]
  exact lemma14_7_3_two S hF

theorem isElemAbelian_fsuU (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (hMod : StmtL32NModule) :
    IsElemAbelian 2 (fsuU T V) := by
  rw [fsuU_eq_conjClosure_hz hMod S.hyp]
  exact hF.F911_2

theorem pCoreOf_sup_le (h : Hyp147 G T L V) : pCoreOf 2 (L ⊔ T) ≤ T := by
  have hT := h.fsu.sylow
  have hTLT : T ≤ L ⊔ T := le_sup_right
  have hidx : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTLT]
    exact Dvd.dvd.mul_right hd _
  exact pCoreOf_le_of_sylow hT.1 hTLT hidx

theorem pCoreOf_sup_le_normalizer_fsuU (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  (pCoreOf_sup_le h).trans ((h.isTSub_V1 hMod).2.2.trans (le_normalizer_conjClosure V _))

theorem lemma14_7_13_one (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (hMod : StmtL32NModule) :
    ⁅L32A.sL T L V, pCoreOf 2 (L ⊔ T)⁆ = conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L := by
  exact commutator_conjClosure_eq (le_normalizer_pCoreOf_sup T L)
    (pCoreOf_sup_le_normalizer_fsuU S.hyp hMod) (sL_le_pCoreOf S hF hMod)

theorem fsuU_comm (h : Hyp147 G T L V) {x y : G} (hx : x ∈ fsuU T V) (hy : y ∈ fsuU T V) :
    x * y = y * x := by
  have := h.abelian
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuU T V)) ⟨y, hy⟩)

theorem commutator_fsuU_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ≤ fsuU T V := by
  rw [Subgroup.commutator_le]
  intro u hu q hq
  have h1 : q * u⁻¹ * q⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (pCoreOf_sup_le_normalizer_fsuU h hMod hq) _).mp
      (inv_mem hu)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc q]
  exact mul_mem hu h1

theorem lemma14_7_13_three (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {l₀ : G} (hl₀ : l₀ ∈ L) (hne : conjSub l₀ (fsuU T V) ≠ fsuU T V)
    (hE : ∀ x ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆, ∀ y ∈ conjSub l₀ (fsuU T V), x * y = y * x) :
    conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ centerOf (L32A.sL T L V) := by
  have hEU := commutator_fsuU_le S.hyp hMod
  have hES : ∀ e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆,
      e ∈ Subgroup.centralizer (L32A.sL T L V : Set G) := by
    intro e he
    show e ∈ Subgroup.centralizer ((Subgroup.closure _ : Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, u, hu, rfl⟩
    by_cases hkU : conjSub k (fsuU T V) = fsuU T V
    · have hx : k * u * k⁻¹ ∈ fsuU T V := by rw [← hkU]; exact mul_mem_conjSub hu
      exact (fsuU_comm S.hyp hx (hEU he))
    · obtain ⟨m, hm, hm1, hm2⟩ := lemma14_7_12_one S hF h13322 hMod (one_mem L) hl₀
        (one_mem L) hk (by rw [conjSub_one]; exact Ne.symm hne)
        (by rw [conjSub_one]; exact Ne.symm hkU)
      rw [mul_one, conjSub_one] at hm1
      have hmU : m ∈ Subgroup.normalizer (fsuU T V : Set G) := conjSub_eq_self_iff.mp hm1
      have hmE : m ∈ Subgroup.normalizer
          ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) :=
        mem_normalizer_commutator hmU (le_normalizer_pCoreOf_sup T L hm)
      have hx : k * u * k⁻¹ ∈ conjSub m (conjSub l₀ (fsuU T V)) := by
        rw [← conjSub_mul, hm2]
        exact mul_mem_conjSub hu
      rw [mem_conjSub] at hx
      have he' : m⁻¹ * e * m ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hmE) e).mp he
        simpa using this
      have h1 := hE _ he' _ hx
      calc k * u * k⁻¹ * e = m * ((m⁻¹ * (k * u * k⁻¹) * m) * (m⁻¹ * e * m)) * m⁻¹ := by
            group
        _ = m * ((m⁻¹ * e * m) * (m⁻¹ * (k * u * k⁻¹) * m)) * m⁻¹ := by rw [h1]
        _ = e * (k * u * k⁻¹) := by group
  refine conjClosure_le fun l hl e he => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mem_conjClosure hl (hEU he)
  · have hlS : l ∈ Subgroup.normalizer (L32A.sL T L V : Set G) :=
      le_normalizer_conjClosure _ _ hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : l⁻¹ * s * l ∈ L32A.sL T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlS) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hES e he) _ hs'
    calc s * (l * e * l⁻¹) = l * ((l⁻¹ * s * l) * e) * l⁻¹ := by group
      _ = l * (e * (l⁻¹ * s * l)) * l⁻¹ := by rw [h1]
      _ = l * e * l⁻¹ * s := by group

theorem conjSub_fsuU_le_normalizer (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {l₀ : G} (hl₀ : l₀ ∈ L) (hne : conjSub l₀ (fsuU T V) ≠ fsuU T V)
    (hN : fsuU T V ≤ Subgroup.normalizer (conjSub l₀ (fsuU T V) : Set G))
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) :
    conjSub x (fsuU T V) ≤ Subgroup.normalizer (conjSub y (fsuU T V) : Set G) := by
  by_cases hxy : conjSub x (fsuU T V) = conjSub y (fsuU T V)
  · rw [hxy]
    exact Subgroup.le_normalizer
  · obtain ⟨l, -, h1, h2⟩ := lemma14_7_12_one S hF h13322 hMod (one_mem L) hl₀ hx hy
      (by rw [conjSub_one]; exact Ne.symm hne) hxy
    rw [mul_one] at h1
    rw [← h1, ← h2, conjSub_mul]
    exact conjSub_le_normalizer hN l

theorem lemma14_7_13_four (S : Setting147 G T L V (L32A.hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (L32A.hz T V)) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {l₀ : G} (hl₀ : l₀ ∈ L) (hne : conjSub l₀ (fsuU T V) ≠ fsuU T V)
    (hN : fsuU T V ≤ Subgroup.normalizer (conjSub l₀ (fsuU T V) : Set G)) :
    frattiniOf (L32A.sL T L V) = ⁅L32A.sL T L V, L32A.sL T L V⁆ ∧
      ⁅L32A.sL T L V, L32A.sL T L V⁆ = conjClosure ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ L := by
  have hUe := isElemAbelian_fsuU S hF hMod
  have hpair := fun {x y : G} (hx : x ∈ L) (hy : y ∈ L) =>
    conjSub_fsuU_le_normalizer S hF h13322 hMod hl₀ hne hN hx hy
  have hAl : ∀ l : G, conjSub l ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ =
      ⁅conjSub l (fsuU T V), conjSub (l * l₀) (fsuU T V)⁆ := by
    intro l
    rw [conjSub_mul]
    exact Subgroup.map_commutator _ _ _
  have hAB : ∀ l ∈ L, conjSub l ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ ≤
      conjClosure ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ L := by
    rintro l hl _ ⟨a, ha, rfl⟩
    exact mem_conjClosure hl ha
  have hle : ⁅L32A.sL T L V, L32A.sL T L V⁆ ≤
      conjClosure ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ L := by
    apply commutator_closure_le
    · rintro _ ⟨k, hk, u, hu, rfl⟩
      apply mem_normalizer_conjClosure
      intro l hl
      rw [hAl l]
      exact mem_normalizer_commutator (hpair hk hl (mul_mem_conjSub hu))
        (hpair hk (mul_mem hl hl₀) (mul_mem_conjSub hu))
    · rintro _ ⟨k, hk, u, hu, rfl⟩ _ ⟨k', hk', u', hu', rfl⟩
      by_cases hkk : conjSub k (fsuU T V) = conjSub k' (fsuU T V)
      · have h1 : k' * u' * k'⁻¹ ∈ conjSub k (fsuU T V) := by
          rw [hkk]
          exact mul_mem_conjSub hu'
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (F7.isElemAbelian_comm (F7.isElemAbelian_conjSub (g := k) hUe) (mul_mem_conjSub hu) h1)]
        exact one_mem _
      · obtain ⟨l, hl, h1, h2⟩ := lemma14_7_12_one S hF h13322 hMod (one_mem L) hl₀ hk hk'
          (by rw [conjSub_one]; exact Ne.symm hne) hkk
        rw [mul_one] at h1
        apply hAB l hl
        rw [hAl l, h1, h2]
        exact Subgroup.commutator_mem_commutator (mul_mem_conjSub hu) (mul_mem_conjSub hu')
  have hge : conjClosure ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ L ≤
      ⁅L32A.sL T L V, L32A.sL T L V⁆ := by
    refine conjClosure_le fun l hl x hx => ?_
    have hUS : fsuU T V ≤ L32A.sL T L V := le_conjClosure _ _
    have hUαS : conjSub l₀ (fsuU T V) ≤ L32A.sL T L V := by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_conjClosure hl₀ hu
    have hlS : l ∈ Subgroup.normalizer (L32A.sL T L V : Set G) :=
      le_normalizer_conjClosure _ _ hl
    exact conj_mem_commutator hlS hlS (Subgroup.commutator_mono hUS hUαS hx)
  refine ⟨frattiniOf_eq_commutator ?_ fun x hx => ?_, le_antisymm hle hge⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (L ⊔ T)).to_le
      (sL_le_pCoreOf S hF hMod)
  · refine sq_mem_commutator_closure ?_ hx
    rintro _ ⟨k, -, u, hu, rfl⟩
    rw [conj_pow, F7.isElemAbelian_pow_eq_one hUe hu]
    group

end Setting

end L32A

end CFSG.Quasithin.H13
