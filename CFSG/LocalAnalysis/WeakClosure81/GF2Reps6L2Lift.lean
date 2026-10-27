module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Transport
public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

open scoped commutatorElement

private theorem exists_mul_of_mem_sup_of_centralizes {X : Type*} [Group X] {H N : Subgroup X}
    (hN : ∀ n ∈ N, ∀ x ∈ H ⊔ N, n * x = x * n) {x : X} (hx : x ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, h * n = x := by
  let S : Subgroup X := H ⊔ N
  have hH : H ≤ S := le_sup_left
  have hconj : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    have h : s * n * s⁻¹ = n := by
      calc s * n * s⁻¹ = (n * s) * s⁻¹ := by rw [← hN n hn s hs]
        _ = n := by group
    rwa [h]
  have hconj' : ∀ s ∈ S, ∀ n : X, s * n * s⁻¹ ∈ N → n ∈ N := by
    intro s hs n hn
    have hs' : s⁻¹ ∈ S := S.inv_mem hs
    have h1 : s⁻¹ * (s * n * s⁻¹) * (s⁻¹)⁻¹ ∈ N := hconj s⁻¹ hs' _ hn
    have h2 : s⁻¹ * (s * n * s⁻¹) * (s⁻¹)⁻¹ = n := by group
    rwa [h2] at h1
  have hNS : (N.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨hconj s hs n, hconj' s hs n⟩
  have hsup : H.subgroupOf S ⊔ N.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hH le_sup_right, Subgroup.subgroupOf_self]
  let xS : ↥S := ⟨x, hx⟩
  have hxS : xS ∈ H.subgroupOf S ⊔ N.subgroupOf S := hsup ▸ Subgroup.mem_top xS
  obtain ⟨h, hh, n, hn, hhn⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := H.subgroupOf S) (t := N.subgroupOf S)).mp hxS
  exact ⟨(h : X), hh, (n : X), hn, by simpa using congrArg Subtype.val hhn⟩

theorem le_of_perfect_le_sup {G : Type*} [Group G] {K H N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hN : ∀ n ∈ N, ∀ x ∈ H ⊔ N, n * x = x * n) (hKH : K ≤ H ⊔ N) : K ≤ H := by
  have hle : ⁅H ⊔ N, H ⊔ N⁆ ≤ ⁅H, H⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨h₁, h₁H, n₁, n₁N, rfl⟩ := exists_mul_of_mem_sup_of_centralizes hN ha
    obtain ⟨h₂, h₂H, n₂, n₂N, rfl⟩ := exists_mul_of_mem_sup_of_centralizes hN hb
    have hn₁h₂ : n₁ * h₂ = h₂ * n₁ := hN n₁ n₁N h₂ (Subgroup.mem_sup_left h₂H)
    have hn₁n₂ : n₁ * n₂ = n₂ * n₁ := hN n₁ n₁N n₂ (Subgroup.mem_sup_right n₂N)
    have hn₂h₁ : n₂ * h₁ = h₁ * n₂ := hN n₂ n₂N h₁ (Subgroup.mem_sup_left h₁H)
    have hn₁ : ⁅n₁, h₂ * n₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      calc n₁ * (h₂ * n₂) = (n₁ * h₂) * n₂ := by rw [mul_assoc]
        _ = (h₂ * n₁) * n₂ := by rw [hn₁h₂]
        _ = h₂ * (n₁ * n₂) := by rw [mul_assoc]
        _ = h₂ * (n₂ * n₁) := by rw [hn₁n₂]
        _ = (h₂ * n₂) * n₁ := by rw [mul_assoc]
    have hn₂ : ⁅h₁, n₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hn₂h₁.symm
    have hcalc : ⁅h₁ * n₁, h₂ * n₂⁆ = ⁅h₁, h₂⁆ := by
      calc ⁅h₁ * n₁, h₂ * n₂⁆
          = h₁ * ⁅n₁, h₂ * n₂⁆ * h₁⁻¹ * ⁅h₁, h₂ * n₂⁆ := by
              rw [commutatorElement_mul_left_eq_conj_mul]
        _ = ⁅h₁, h₂ * n₂⁆ := by rw [hn₁]; simp
        _ = ⁅h₁, h₂⁆ * h₂ * ⁅h₁, n₂⁆ * h₂⁻¹ := by
              rw [commutatorElement_mul_right_eq_mul_conj]
        _ = ⁅h₁, h₂⁆ := by rw [hn₂]; simp
    rw [hcalc]
    exact Subgroup.commutator_mem_commutator h₁H h₂H
  calc K = ⁅K, K⁆ := hK.symm
    _ ≤ ⁅H ⊔ N, H ⊔ N⁆ := Subgroup.commutator_mono hKH hKH
    _ ≤ ⁅H, H⁆ := hle
    _ ≤ H := Subgroup.commutator_le_self H

theorem mem_of_odd_of_mem_sup {G : Type*} [Group G] {H N : Subgroup G}
    (hN : ∀ n ∈ N, ∀ x ∈ H ⊔ N, n * x = x * n) (hN2 : ∀ n ∈ N, n * n = 1) {x : G}
    (hx : x ∈ H ⊔ N) (hodd : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨h, hh, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_centralizes hN hx
  have hcomm : Commute h n := (hN n hn h (Subgroup.mem_sup_left hh)).symm
  obtain ⟨k, hk⟩ := hodd
  have hn2 : n ^ 2 = 1 := by rw [pow_two]; exact hN2 n hn
  have hnm : n ^ orderOf (h * n) = n := by
    rw [hk, pow_succ, pow_mul, hn2, one_pow, one_mul]
  have hp := pow_orderOf_eq_one (h * n)
  rw [hcomm.mul_pow, hnm] at hp
  have hnH : n ∈ H := by
    rw [eq_inv_of_mul_eq_one_right hp]
    exact H.inv_mem (H.pow_mem hh _)
  exact H.mul_mem hh hnH

variable {P : Type*} [Group P]


private abbrev QE (t u : P) : Subgroup P := Subgroup.closure ({t, u} : Set P)

private abbrev QG (L : Subgroup P) (t u : P) : Subgroup P := QE t u ⊔ L

private abbrev QN (L : Subgroup P) (t u : P) : Subgroup P :=
  QG L t u ⊓ Subgroup.centralizer (L : Set P)

private abbrev QI (L : Subgroup P) : Subgroup (MulAut ↥L) :=
  (MulAut.conj : ↥L →* MulAut ↥L).range

section LiftingAux

variable {L : Subgroup P} {t u : P}

private abbrev QEbar (L : Subgroup P) (t u : P)
    (htN : t ∈ normalizer (L : Set P)) (huN : u ∈ normalizer (L : Set P)) :
    Subgroup (MulAut ↥L) :=
  Subgroup.closure ({conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩} : Set (MulAut ↥L))

private noncomputable def liftAlpha (hGN : QG L t u ≤ normalizer (L : Set P)) :
    ↥(QG L t u) →* MulAut ↥L :=
  (conjAct L).comp (Subgroup.inclusion hGN)

private theorem QE_le_QG : QE t u ≤ QG L t u := le_sup_left

private theorem L_le_QG : L ≤ QG L t u := le_sup_right

private theorem commutator_L_eq (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) :
    ⁅L, L⁆ = L := by
  have hnab : ¬ IsMulCommutative ↥L := by
    intro hcomm
    have htop : center ↥L = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    rw [hZ] at htop
    exact bot_ne_top htop
  exact Subgroup.commutator_eq_self (H := L)
    (hH := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnab)

private theorem QE_le_normalizer (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) : QE t u ≤ normalizer (L : Set P) :=
  (Subgroup.closure_le (normalizer (L : Set P))).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact htN
    · exact huN)

private theorem QG_le_normalizer (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) : QG L t u ≤ normalizer (L : Set P) :=
  sup_le (QE_le_normalizer htN huN) Subgroup.le_normalizer

private theorem QE_comm (htu : t * u = u * t) :
    ∀ x ∈ QE t u, ∀ y ∈ QE t u, x * y = y * x := by
  have hgen : ({t, u} : Set P) ⊆ (Subgroup.centralizer ({t, u} : Set P) : Set P) := by
    intro z hz
    change z ∈ Subgroup.centralizer ({t, u} : Set P)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    · rfl
    · exact htu.symm
    · exact htu
    · rfl
  have hcl : Subgroup.centralizer (QE t u : Set P) = Subgroup.centralizer ({t, u} : Set P) :=
    Subgroup.centralizer_closure ({t, u} : Set P)
  have hE : QE t u ≤ Subgroup.centralizer (QE t u : Set P) := by
    rw [hcl]
    exact (Subgroup.closure_le (Subgroup.centralizer ({t, u} : Set P))).mpr hgen
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hE hx) y hy).symm

private theorem QE_elemAbelian (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t) : CFSG.Open.IsElemAbelian 2 (QE t u) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    exact QE_comm htu a (Subgroup.subset_closure ha) b (Subgroup.subset_closure hb)
  · intro a ha
    rw [pow_two]
    rcases ha with rfl | rfl
    · exact htt
    · exact huu

private theorem QE_mul_self (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t) {e : P} (he : e ∈ QE t u) : e * e = 1 :=
  (QE_elemAbelian htt huu htu).mul_self_eq_one he

private theorem inf_centralizer_eq_bot (hZ : center ↥L = ⊥) :
    L ⊓ Subgroup.centralizer (L : Set P) = ⊥ := by
  have hcent : (Subgroup.centralizer (L : Set P)).subgroupOf L = Subgroup.center ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    constructor
    · intro h y
      exact Subtype.ext (h (y : P) y.2)
    · intro h l hl
      exact congrArg Subtype.val (h ⟨l, hl⟩)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [← hcent]
    exact hx.2
  rw [hZ] at hxcenter
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter)

private theorem conj_mem_L {g l : P} (hg : g ∈ normalizer (L : Set P)) (hl : l ∈ L) :
    g * l * g⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp hg l).mp hl

private theorem commutator_mem_L_of_normalizer {a g : P} (ha : a ∈ L)
    (hg : g ∈ normalizer (L : Set P)) : ⁅a, g⁆ ∈ L := by
  have hconj : g * a⁻¹ * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hg a⁻¹).mp (L.inv_mem ha)
  rw [commutatorElement_def]
  simpa only [mul_assoc] using L.mul_mem ha hconj

private theorem exists_mul_QE_L (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) {x : P} (hx : x ∈ QG L t u) :
    ∃ e ∈ QE t u, ∃ l ∈ L, e * l = x := by
  have hLnorm : ((L.subgroupOf (QG L t u))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (H := L) (K := QG L t u) le_sup_right]
    exact QG_le_normalizer htN huN
  have hsup : (QE t u).subgroupOf (QG L t u) ⊔ L.subgroupOf (QG L t u) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := QE t u) (A' := L) (B := QG L t u)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (QG L t u)
  have hxG : (⟨x, hx⟩ : ↥(QG L t u)) ∈
      (QE t u).subgroupOf (QG L t u) ⊔ L.subgroupOf (QG L t u) := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨e, he, l, hl, hel⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := (QE t u).subgroupOf (QG L t u))
      (t := L.subgroupOf (QG L t u)) (ht := hLnorm)).mp hxG
  exact ⟨(e : P), he, (l : P), hl, congrArg Subtype.val hel⟩

private theorem commutator_mem_L (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htu : t * u = u * t) {x y : P}
    (hx : x ∈ QG L t u) (hy : y ∈ QG L t u) : x * y * x⁻¹ * y⁻¹ ∈ L := by
  obtain ⟨e₁, he₁, l₁, hl₁, rfl⟩ := exists_mul_QE_L htN huN hx
  obtain ⟨e₂, he₂, l₂, hl₂, rfl⟩ := exists_mul_QE_L htN huN hy
  have he₁N : e₁ ∈ normalizer (L : Set P) := QE_le_normalizer htN huN he₁
  have he₂N : e₂ ∈ normalizer (L : Set P) := QE_le_normalizer htN huN he₂
  change ⁅e₁ * l₁, e₂ * l₂⁆ ∈ L
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_mul_right_eq_mul_conj]
  have hecomm : ⁅e₁, e₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (QE_comm htu e₁ he₁ e₂ he₂)
  rw [hecomm, one_mul]
  have h1 : ⁅l₁, e₂⁆ ∈ L := commutator_mem_L_of_normalizer hl₁ he₂N
  have h2 : e₂ * ⁅l₁, l₂⁆ * e₂⁻¹ ∈ L :=
    conj_mem_L he₂N
      (Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator hl₁ hl₂))
  have hinner1 : ⁅l₁, e₂⁆ * e₂ * ⁅l₁, l₂⁆ * e₂⁻¹ ∈ L := by
    simpa only [mul_assoc] using L.mul_mem h1 h2
  have h3' : ⁅l₂, e₁⁆ ∈ L :=
    commutator_mem_L_of_normalizer (a := l₂) (g := e₁) hl₂ he₁N
  have h3 : ⁅e₁, l₂⁆ ∈ L := by
    rw [← commutatorElement_inv]
    exact L.inv_mem h3'
  have hinner2 : e₂ * ⁅e₁, l₂⁆ * e₂⁻¹ ∈ L := conj_mem_L he₂N h3
  simpa only [mul_assoc] using L.mul_mem (conj_mem_L he₁N hinner1) hinner2

private theorem conjAct_mk_eq_conj {l : P} (hl : l ∈ L) :
    conjAct L ⟨l, Subgroup.le_normalizer hl⟩ =
      (MulAut.conj : ↥L →* MulAut ↥L) ⟨l, hl⟩ := by
  ext v
  rw [AutOn.coe_conjAct_apply, MulAut.conj_apply]
  rfl

private theorem conj_injective (hZ : center ↥L = ⊥) :
    Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
  rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]

private theorem map_subgroupOf_liftAlpha_eq_range
    (hGN : QG L t u ≤ normalizer (L : Set P)) :
    (L.subgroupOf (QG L t u)).map (liftAlpha hGN) = QI L := by
  ext f
  constructor
  · intro hf
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hf
    have hl' : (l : P) ∈ L := Subgroup.mem_subgroupOf.mp hl
    refine ⟨⟨(l : P), hl'⟩, ?_⟩
    show (MulAut.conj : ↥L →* MulAut ↥L) ⟨(l : P), hl'⟩ =
      conjAct L ⟨(l : P), hGN l.2⟩
    rw [show (⟨(l : P), hGN l.2⟩ : normalizer (L : Set P)) =
        ⟨(l : P), Subgroup.le_normalizer hl'⟩ from Subtype.ext rfl]
    exact (conjAct_mk_eq_conj hl').symm
  · rintro ⟨l, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨(l : P), L_le_QG l.2⟩, l.2, ?_⟩
    show conjAct L ⟨(l : P), hGN (L_le_QG l.2)⟩ =
      (MulAut.conj : ↥L →* MulAut ↥L) l
    rw [show (⟨(l : P), hGN (L_le_QG l.2)⟩ : normalizer (L : Set P)) =
        ⟨(l : P), Subgroup.le_normalizer l.2⟩ from Subtype.ext rfl]
    exact conjAct_mk_eq_conj l.2

private theorem subgroupOf_closure_eq {B : Subgroup P} {S : Set P} (hS : S ⊆ B) :
    (Subgroup.closure S).subgroupOf B =
      Subgroup.closure ((Subtype.val) ⁻¹' S : Set ↥B) := by
  apply Subgroup.map_injective (Subgroup.subtype_injective B)
  rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le B).mpr hS),
    MonoidHom.map_closure]
  have himg : (⇑B.subtype : ↥B → P) '' ((Subtype.val) ⁻¹' S : Set ↥B) = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hS hy⟩, hy, rfl⟩
  rw [himg]

private theorem map_QE_eq_closure (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (hGN : QG L t u ≤ normalizer (L : Set P)) :
    ((QE t u).subgroupOf (QG L t u)).map (liftAlpha hGN) = QEbar L t u htN huN := by
  have htQE : t ∈ QE t u := Subgroup.subset_closure (by simp)
  have huQE : u ∈ QE t u := Subgroup.subset_closure (by simp)
  let tG : ↥(QG L t u) := ⟨t, QE_le_QG htQE⟩
  let uG : ↥(QG L t u) := ⟨u, QE_le_QG huQE⟩
  have hsub : (QE t u).subgroupOf (QG L t u) =
      Subgroup.closure ((Subtype.val) ⁻¹' ({t, u} : Set P) : Set ↥(QG L t u)) :=
    subgroupOf_closure_eq (B := QG L t u) (S := ({t, u} : Set P)) (by
      intro x hx
      rcases hx with rfl | rfl
      · exact QE_le_QG htQE
      · exact QE_le_QG huQE)
  have hpre : ((Subtype.val) ⁻¹' ({t, u} : Set P) : Set ↥(QG L t u)) =
      ({tG, uG} : Set ↥(QG L t u)) := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · left
        exact Subtype.ext hx
      · right
        exact Subtype.ext hx
    · intro hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  have htval : liftAlpha hGN tG = conjAct L ⟨t, htN⟩ := by
    change conjAct L ⟨t, hGN tG.2⟩ = conjAct L ⟨t, htN⟩
    exact congrArg (conjAct L) (Subtype.ext rfl)
  have huval : liftAlpha hGN uG = conjAct L ⟨u, huN⟩ := by
    change conjAct L ⟨u, hGN uG.2⟩ = conjAct L ⟨u, huN⟩
    exact congrArg (conjAct L) (Subtype.ext rfl)
  rw [hsub, hpre, MonoidHom.map_closure, Set.image_pair, htval, huval]

private theorem map_top_eq_closure_range (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (hGN : QG L t u ≤ normalizer (L : Set P)) :
    (⊤ : Subgroup ↥(QG L t u)).map (liftAlpha hGN) = QEbar L t u htN huN ⊔ QI L := by
  rw [← Subgroup.subgroupOf_self (QG L t u)]
  change ((QE t u ⊔ L).subgroupOf (QG L t u)).map (liftAlpha hGN) = QEbar L t u htN huN ⊔ QI L
  rw [Subgroup.subgroupOf_sup (A := QE t u) (A' := L) (B := QG L t u)
      le_sup_left le_sup_right,
    Subgroup.map_sup, map_QE_eq_closure htN huN hGN,
    map_subgroupOf_liftAlpha_eq_range hGN]

private theorem quadY_le {G E : Subgroup P} {a : P} (hE : E ≤ G) : quadY G E a ≤ G := by
  unfold quadY
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun _ => ?_
  intro y hy
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
  exact G.mul_mem (G.mul_mem hx (hE he)) (G.inv_mem hx)

private theorem quadY_subgroupOf {G E : Subgroup P} {a : P} (hE : E ≤ G) (ha : a ∈ G) :
    (quadY G E a).subgroupOf G = quadY ⊤ (E.subgroupOf G) ⟨a, ha⟩ := by
  let T : Subgroup ↥G := quadY ⊤ (E.subgroupOf G) ⟨a, ha⟩
  have hf : ∀ x ∈ (⊤ : Subgroup ↥G),
      (Subgroup.subtype G) x * (Subgroup.subtype G) ⟨a, ha⟩ =
        (Subgroup.subtype G) ⟨a, ha⟩ * (Subgroup.subtype G) x →
      x * ⟨a, ha⟩ = ⟨a, ha⟩ * x := by
    intro x _ hx
    exact Subtype.ext hx
  have hmap := quadY_map (G := ⊤) (B := E.subgroupOf G) (a := ⟨a, ha⟩)
    (Subgroup.subtype G) hf
  simp only [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hE] at hmap
  have hYle : quadY G E a ≤ G := quadY_le hE
  have hmapA : ((quadY G E a).subgroupOf G).map G.subtype = quadY G E a :=
    Subgroup.map_subgroupOf_eq_of_le hYle
  have hmapT : (quadY ⊤ (E.subgroupOf G) ⟨a, ha⟩).map G.subtype = quadY G E a := by
    simpa using hmap
  exact Subgroup.map_injective (Subgroup.subtype_injective G) (hmapA.trans hmapT.symm)

private theorem commute_of_commute_images (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htu : t * u = u * t)
    (hZ : center ↥L = ⊥) (hGN : QG L t u ≤ normalizer (L : Set P)) {x a : P} (hx : x ∈ QG L t u)
    (ha : a ∈ QE t u) (hcomm : liftAlpha hGN ⟨x, hx⟩ * liftAlpha hGN ⟨a, QE_le_QG ha⟩ =
      liftAlpha hGN ⟨a, QE_le_QG ha⟩ * liftAlpha hGN ⟨x, hx⟩) : x * a = a * x := by
  have hmem : ⁅x, a⁆ ∈ QG L t u :=
    Subgroup.commutator_le_self (QG L t u)
      (Subgroup.commutator_mem_commutator hx (QE_le_QG ha))
  have hker : liftAlpha hGN ⟨⁅x, a⁆, hmem⟩ = 1 := by
    have hsub : (⟨⁅x, a⁆, hmem⟩ : ↥(QG L t u)) =
        ⁅(⟨x, hx⟩ : ↥(QG L t u)), (⟨a, QE_le_QG ha⟩ : ↥(QG L t u))⁆ :=
      Subtype.ext rfl
    rw [hsub, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hzC : ⁅x, a⁆ ∈ Subgroup.centralizer (L : Set P) := by
    have hker' : conjAct L ⟨⁅x, a⁆, hGN hmem⟩ = 1 := by
      show conjAct L (Subgroup.inclusion hGN ⟨⁅x, a⁆, hmem⟩) = 1
      exact hker
    exact (AutOn.conjAct_eq_one_iff ⟨⁅x, a⁆, hGN hmem⟩).mp hker'
  have hzL : ⁅x, a⁆ ∈ L := by
    have := commutator_mem_L (L := L) (t := t) (u := u) htN huN htu hx (QE_le_QG ha)
    simpa [commutatorElement_def] using this
  have hzbot : ⁅x, a⁆ ∈ (⊥ : Subgroup P) := by
    rw [← inf_centralizer_eq_bot hZ]
    exact ⟨hzL, hzC⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hzbot)

private theorem map_quadY_eq (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htu : t * u = u * t)
    (hZ : center ↥L = ⊥) (hGN : QG L t u ≤ normalizer (L : Set P)) {a : P}
    (ha : a ∈ QE t u) :
    ((quadY (QG L t u) (QE t u) a).subgroupOf (QG L t u)).map (liftAlpha hGN) =
      quadY (QEbar L t u htN huN ⊔ QI L) (QEbar L t u htN huN)
        (conjAct L ⟨a, hGN (QE_le_QG ha)⟩) := by
  rw [quadY_subgroupOf (E := QE t u) (G := QG L t u) le_sup_left (QE_le_QG ha)]
  have hcomm : ∀ x ∈ (⊤ : Subgroup ↥(QG L t u)),
      liftAlpha hGN x * liftAlpha hGN ⟨a, QE_le_QG ha⟩ =
        liftAlpha hGN ⟨a, QE_le_QG ha⟩ * liftAlpha hGN x →
      x * ⟨a, QE_le_QG ha⟩ = ⟨a, QE_le_QG ha⟩ * x := by
    intro x _ hx
    exact Subtype.ext (commute_of_commute_images htN huN htu hZ hGN x.2 ha hx)
  rw [quadY_map (liftAlpha hGN) hcomm, map_top_eq_closure_range htN huN hGN,
    map_QE_eq_closure htN huN hGN]
  rfl

private theorem centralizes_G_of_mem_QN (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htu : t * u = u * t)
    (hZ : center ↥L = ⊥) (hGN : QG L t u ≤ normalizer (L : Set P)) {n : P}
    (hn : n ∈ QN L t u) : ∀ x ∈ QG L t u, n * x = x * n := by
  have hnG : n ∈ QG L t u := hn.1
  have hnC : n ∈ Subgroup.centralizer (L : Set P) := hn.2
  intro x hx
  have hx_cent : x * n * x⁻¹ ∈ Subgroup.centralizer (L : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : x⁻¹ * l * x ∈ L :=
      (Subgroup.mem_normalizer_iff''.mp (hGN hx) l).mp hl
    have hcomm := Subgroup.mem_centralizer_iff.mp hnC (x⁻¹ * l * x) hxl
    calc l * (x * n * x⁻¹) = l * x * n * x⁻¹ := by group
      _ = x * (x⁻¹ * l * x) * n * x⁻¹ := by group
      _ = x * ((x⁻¹ * l * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * l * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * n * x⁻¹) * l := by group
  have hcommC : ⁅n, x⁆ ∈ Subgroup.centralizer (L : Set P) := by
    have hmemC : n * (x * n * x⁻¹)⁻¹ ∈ Subgroup.centralizer (L : Set P) :=
      (Subgroup.centralizer (L : Set P)).mul_mem hnC
        ((Subgroup.centralizer (L : Set P)).inv_mem hx_cent)
    simpa [commutatorElement_def, mul_inv_rev, mul_assoc] using hmemC
  have hcommL : ⁅n, x⁆ ∈ L := by
    have := commutator_mem_L (L := L) (t := t) (u := u) htN huN htu hnG hx
    simpa [commutatorElement_def] using this
  have hbot : ⁅n, x⁆ ∈ (⊥ : Subgroup P) := by
    rw [← inf_centralizer_eq_bot hZ]
    exact ⟨hcommL, hcommC⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)

private theorem sq_one_QN (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t) (hZ : center ↥L = ⊥) {n : P} (hn : n ∈ QN L t u) :
    n * n = 1 := by
  obtain ⟨e, he, l, hl, rfl⟩ := exists_mul_QE_L htN huN hn.1
  have hnC : e * l ∈ Subgroup.centralizer (L : Set P) := hn.2
  have he2 : e * e = 1 := QE_mul_self htt huu htu he
  have hconj : e * l * e⁻¹ ∈ L := conj_mem_L (QE_le_normalizer htN huN he) hl
  have hsqL : (e * l) * (e * l) ∈ L := by
    have hcalc : (e * l) * (e * l) = (e * l * e⁻¹) * l := by
      calc (e * l) * (e * l) = (e * l * e⁻¹) * (e * e) * l := by group
        _ = (e * l * e⁻¹) * l := by rw [he2, mul_one]
    rw [hcalc]
    exact L.mul_mem hconj hl
  have hsqC : (e * l) * (e * l) ∈ Subgroup.centralizer (L : Set P) :=
    (Subgroup.centralizer (L : Set P)).mul_mem hnC hnC
  have hbot : (e * l) * (e * l) ∈ (⊥ : Subgroup P) := by
    rw [← inf_centralizer_eq_bot hZ]
    exact ⟨hsqL, hsqC⟩
  exact Subgroup.mem_bot.mp hbot

private theorem le_of_image_le (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥)
    (htN : t ∈ normalizer (L : Set P)) (huN : u ∈ normalizer (L : Set P))
    (htu : t * u = u * t) (hGN : QG L t u ≤ normalizer (L : Set P)) {H : Subgroup P}
    (hH : H ≤ QG L t u)
    (himg : (L.subgroupOf (QG L t u)).map (liftAlpha hGN) ≤
      (H.subgroupOf (QG L t u)).map (liftAlpha hGN)) : L ≤ H := by
  have hLH : L ≤ H ⊔ QN L t u := by
    intro l hl
    have hlG : l ∈ QG L t u := L_le_QG hl
    have hmemL : liftAlpha hGN ⟨l, hlG⟩ ∈
        (L.subgroupOf (QG L t u)).map (liftAlpha hGN) :=
      Subgroup.mem_map.mpr ⟨⟨l, hlG⟩, hl, rfl⟩
    obtain ⟨g, hgH, hgeq⟩ := Subgroup.mem_map.mp (himg hmemL)
    have hker : liftAlpha hGN (g⁻¹ * ⟨l, hlG⟩) = 1 := by
      rw [map_mul, map_inv, hgeq, inv_mul_cancel]
    have hzC : ((g⁻¹ * ⟨l, hlG⟩ : ↥(QG L t u)) : P) ∈
        Subgroup.centralizer (L : Set P) := by
      have hker' : conjAct L ⟨((g⁻¹ * ⟨l, hlG⟩ : ↥(QG L t u)) : P),
          hGN (g⁻¹ * ⟨l, hlG⟩).2⟩ = 1 := by
        show conjAct L (Subgroup.inclusion hGN (g⁻¹ * ⟨l, hlG⟩)) = 1
        exact hker
      exact (AutOn.conjAct_eq_one_iff _).mp hker'
    have hnN : (g : P)⁻¹ * l ∈ QN L t u := by
      refine ⟨?_, ?_⟩
      · simpa using (QG L t u).mul_mem ((QG L t u).inv_mem g.2) hlG
      · simpa using hzC
    have hgnH : (g : P) ∈ H := hgH
    have hl_eq : l = (g : P) * ((g : P)⁻¹ * l) := by group
    rw [hl_eq]
    exact (H ⊔ QN L t u).mul_mem (Subgroup.mem_sup_left hgnH)
      (Subgroup.mem_sup_right hnN)
  refine le_of_perfect_le_sup (K := L) (H := H) (N := QN L t u)
    (commutator_L_eq hL hZ) ?_ hLH
  intro n hn x hx
  exact centralizes_G_of_mem_QN htN huN htu hZ hGN hn x
    ((sup_le hH inf_le_left) hx)

private theorem conjAct_mulAut_conj {g : P} (hg : g ∈ normalizer (L : Set P)) (l : ↥L) :
    conjAct L ⟨g, hg⟩ * (MulAut.conj : ↥L →* MulAut ↥L) l *
        (conjAct L ⟨g, hg⟩)⁻¹ =
      (MulAut.conj : ↥L →* MulAut ↥L)
        ⟨g * (l : P) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (l : P)).mp l.2⟩ := by
  ext x
  rw [← map_inv (conjAct L) ⟨g, hg⟩]
  simp only [MulAut.conj_apply, MulAut.mul_apply, AutOn.coe_conjAct_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  group


private theorem conj_mulAut_apply (φ : MulAut ↥L) (y : ↥L) :
    (MulAut.conj φ) (MulAut.conj y) = (MulAut.conj : ↥L →* MulAut ↥L) (φ y) := by
  ext z
  simp only [MulAut.conj_apply, MulAut.mul_apply]
  rw [map_mul, map_mul, map_inv]
  simp

private theorem map_conj_mulAut (K : Subgroup ↥L) (φ : MulAut ↥L) :
    (K.map φ.toMonoidHom).map (MulAut.conj : ↥L →* MulAut ↥L) =
      (K.map (MulAut.conj : ↥L →* MulAut ↥L)).map
        (MulAut.conj φ).toMonoidHom := by
  have hhom : (MulAut.conj : ↥L →* MulAut ↥L).comp φ.toMonoidHom =
      (MulAut.conj φ).toMonoidHom.comp (MulAut.conj : ↥L →* MulAut ↥L) := by
    apply MonoidHom.ext
    intro x
    exact (conj_mulAut_apply φ x).symm
  rw [Subgroup.map_map, Subgroup.map_map, hhom]

private theorem subgroupOf_map_conj {H : Subgroup P} (hH : H ≤ L) {g : P}
    (hg : g ∈ normalizer (L : Set P)) :
    (H.map (MulAut.conj g).toMonoidHom).subgroupOf L =
      (H.subgroupOf L).map (conjAct L ⟨g, hg⟩) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨h, hH hh⟩, hh, ?_⟩
    apply Subtype.ext
    show (g * h * g⁻¹ : P) = (x : P)
    simpa [MulAut.conj_apply] using hxh
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨(y : P), hy, ?_⟩
    have hyx' := congrArg Subtype.val hyx
    show (g * (y : P) * g⁻¹ : P) = (x : P)
    simpa [AutOn.coe_conjAct_apply, MulAut.conj_apply] using hyx'

private theorem map_subgroupOf_map_conj {H : Subgroup P} (hH : H ≤ L) {g : P}
    (hg : g ∈ normalizer (L : Set P)) :
    ((H.map (MulAut.conj g).toMonoidHom).subgroupOf L).map
        (MulAut.conj : ↥L →* MulAut ↥L) =
      ((H.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)).map
        (MulAut.conj (conjAct L ⟨g, hg⟩)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [subgroupOf_map_conj hH hg] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj : ↥L →* MulAut ↥L) y, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    · have hval : ((conjAct L ⟨g, hg⟩) y : ↥L) =
          ⟨g * (y : P) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (y : P)).mp y.2⟩ :=
        Subtype.ext rfl
      exact (conjAct_mulAut_conj hg y).trans (congrArg MulAut.conj hval.symm)
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Subgroup.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    refine Subgroup.mem_map.mpr ⟨(conjAct L ⟨g, hg⟩) y, ?_, ?_⟩
    · rw [subgroupOf_map_conj hH hg]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    · exact (conjAct_mulAut_conj hg y).symm.trans hzw

private theorem subgroupOf_map_subtype' (C : Subgroup ↥L) :
    (C.map L.subtype).subgroupOf L = C := by
  change Subgroup.comap L.subtype (Subgroup.map L.subtype C) = C
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective C

end LiftingAux

theorem exists_parrott_of_conjAct {L : Subgroup P} (hL : IsSimpleGroup ↥L)
    (hZ : center ↥L = ⊥) {t u : P} (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t)
    (h : ParrottGen (MulAut.conj : ↥L →* MulAut ↥L).range (conjAct L ⟨t, htN⟩)
      (conjAct L ⟨u, huN⟩)) :
    ∃ τ ∈ L, Odd (orderOf τ) ∧ t * τ * t⁻¹ = τ⁻¹ ∧ L ≤ closure {t, u, τ} := by
  obtain ⟨τbar, hτbar, hodd, hinv, hgen⟩ := h
  obtain ⟨τ₁, rfl⟩ := MonoidHom.mem_range.mp hτbar
  have hord : orderOf (τ₁ : P) = orderOf ((MulAut.conj : ↥L →* MulAut ↥L) τ₁) := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective (MulAut.conj : ↥L →* MulAut ↥L) (conj_injective hZ) τ₁).symm
  have htτL : t * (τ₁ : P) * t⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp htN (τ₁ : P)).mp τ₁.2
  have hτinvL : (τ₁ : P)⁻¹ ∈ L := L.inv_mem τ₁.2
  have hconj_eq : (MulAut.conj : ↥L →* MulAut ↥L) ⟨t * (τ₁ : P) * t⁻¹, htτL⟩ =
      conjAct L ⟨t, htN⟩ * (MulAut.conj : ↥L →* MulAut ↥L) τ₁ *
        (conjAct L ⟨t, htN⟩)⁻¹ := by
    ext x
    rw [← map_inv (conjAct L) ⟨t, htN⟩]
    simp only [MulAut.conj_apply, MulAut.mul_apply, AutOn.coe_conjAct_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  have hmain : (MulAut.conj : ↥L →* MulAut ↥L) ⟨t * (τ₁ : P) * t⁻¹, htτL⟩ =
      (MulAut.conj : ↥L →* MulAut ↥L) ⟨(τ₁ : P)⁻¹, hτinvL⟩ := by
    rw [hconj_eq, hinv]
    exact (map_inv (MulAut.conj : ↥L →* MulAut ↥L) τ₁).symm
  have hconjP : t * (τ₁ : P) * t⁻¹ = (τ₁ : P)⁻¹ :=
    congrArg Subtype.val (conj_injective hZ hmain)
  let H : Subgroup P := closure ({t, u, (τ₁ : P)} : Set P)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hτH : (τ₁ : P) ∈ H := Subgroup.subset_closure (by simp)
  have hHleG : H ≤ QG L t u := by
    refine (Subgroup.closure_le (QG L t u)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right τ₁.2
  have hGN : QG L t u ≤ normalizer (L : Set P) := QG_le_normalizer htN huN
  have hclosure_le : Subgroup.closure
      ({conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩,
        (MulAut.conj : ↥L →* MulAut ↥L) τ₁} : Set (MulAut ↥L)) ≤
      (H.subgroupOf (QG L t u)).map (liftAlpha hGN) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    · refine Subgroup.mem_map.mpr ⟨⟨t, hHleG htH⟩, htH, ?_⟩
      show conjAct L ⟨t, hGN (hHleG htH)⟩ = conjAct L ⟨t, htN⟩
      exact congrArg (conjAct L) (Subtype.ext rfl)
    · refine Subgroup.mem_map.mpr ⟨⟨u, hHleG huH⟩, huH, ?_⟩
      show conjAct L ⟨u, hGN (hHleG huH)⟩ = conjAct L ⟨u, huN⟩
      exact congrArg (conjAct L) (Subtype.ext rfl)
    · refine Subgroup.mem_map.mpr ⟨⟨(τ₁ : P), hHleG hτH⟩, hτH, ?_⟩
      show conjAct L ⟨(τ₁ : P), hGN (hHleG hτH)⟩ =
        (MulAut.conj : ↥L →* MulAut ↥L) τ₁
      rw [show (⟨(τ₁ : P), hGN (hHleG hτH)⟩ : normalizer (L : Set P)) =
          ⟨(τ₁ : P), Subgroup.le_normalizer τ₁.2⟩ from Subtype.ext rfl]
      exact conjAct_mk_eq_conj τ₁.2
  have himg : (L.subgroupOf (QG L t u)).map (liftAlpha hGN) ≤
      (H.subgroupOf (QG L t u)).map (liftAlpha hGN) := by
    rw [map_subgroupOf_liftAlpha_eq_range hGN]
    exact hgen.trans hclosure_le
  exact ⟨(τ₁ : P), τ₁.2, hord ▸ hodd, hconjP,
    le_of_image_le hL hZ htN huN htu hGN hHleG himg⟩

theorem le_quadY_sup_of_conjAct {L : Subgroup P} (hL : IsSimpleGroup ↥L)
    (hZ : center ↥L = ⊥) {t u : P} (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t)
    (h : (MulAut.conj : ↥L →* MulAut ↥L).range ≤
      quadY (closure {conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩} ⊔
          (MulAut.conj : ↥L →* MulAut ↥L).range)
        (closure {conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩}) (conjAct L ⟨t, htN⟩) ⊔
      quadY (closure {conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩} ⊔
          (MulAut.conj : ↥L →* MulAut ↥L).range)
        (closure {conjAct L ⟨t, htN⟩, conjAct L ⟨u, huN⟩}) (conjAct L ⟨u, huN⟩)) :
    L ≤ quadY (closure {t, u} ⊔ L) (closure {t, u}) t ⊔
      quadY (closure {t, u} ⊔ L) (closure {t, u}) u := by
  let H : Subgroup P := quadY (QG L t u) (QE t u) t ⊔ quadY (QG L t u) (QE t u) u
  have htQE : t ∈ QE t u := Subgroup.subset_closure (by simp)
  have huQE : u ∈ QE t u := Subgroup.subset_closure (by simp)
  have hYtG : quadY (QG L t u) (QE t u) t ≤ QG L t u := quadY_le le_sup_left
  have hYuG : quadY (QG L t u) (QE t u) u ≤ QG L t u := quadY_le le_sup_left
  have hHleG : H ≤ QG L t u := sup_le hYtG hYuG
  have hGN : QG L t u ≤ normalizer (L : Set P) := QG_le_normalizer htN huN
  have hmap_t := map_quadY_eq htN huN htu hZ hGN htQE
  have hmap_u := map_quadY_eq htN huN htu hZ hGN huQE
  have himg : (L.subgroupOf (QG L t u)).map (liftAlpha hGN) ≤
      (H.subgroupOf (QG L t u)).map (liftAlpha hGN) := by
    rw [map_subgroupOf_liftAlpha_eq_range hGN]
    change QI L ≤
      ((quadY (QG L t u) (QE t u) t ⊔ quadY (QG L t u) (QE t u) u).subgroupOf
        (QG L t u)).map (liftAlpha hGN)
    rw [Subgroup.subgroupOf_sup hYtG hYuG, Subgroup.map_sup, hmap_t, hmap_u]
    simpa [QEbar] using h
  simpa [H] using le_of_image_le hL hZ htN huN htu hGN hHleG himg

theorem exists_of_l2CaseIII_conjAct {L : Subgroup P} (hL : IsSimpleGroup ↥L)
    (hZ : center ↥L = ⊥) {t u : P} (htN : t ∈ normalizer (L : Set P))
    (huN : u ∈ normalizer (L : Set P)) (htt : t * t = 1) (huu : u * u = 1)
    (htu : t * u = u * t)
    (h : L2CaseIII (MulAut.conj : ↥L →* MulAut ↥L).range (conjAct L ⟨t, htN⟩)
      (conjAct L ⟨u, huN⟩)) :
    ∃ (p : ℕ) (U U₀ : Subgroup P), p.Prime ∧ p ≠ 2 ∧ U ≤ L ∧ U ≠ ⊥ ∧
      (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x ^ p = 1) ∧
      (∀ x ∈ U, u * x * u⁻¹ ∈ U) ∧ U₀ ≤ U ∧ (∀ x ∈ U₀, x * u = u * x) ∧
      U₀ ≤ quadY (closure {t, u} ⊔ L) (closure {t, u}) u ∧
      ∀ H : Subgroup P, H ≤ U → H.relIndex U = p → ∃ s ∈ L, (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧
        ¬ U₀ ≤ H.map (MulAut.conj s).toMonoidHom ∧
        (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj u).toMonoidHom ≠
          H.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨p, Ubar, hp, hp2, hUbar_le, hUbar_ne, hUbar_comm, hUbar_exp, hUbar_norm,
    hUbar_cent, hUbar_hyp⟩ := h
  let C : Subgroup ↥L := Ubar.comap (MulAut.conj : ↥L →* MulAut ↥L)
  let C₀ : Subgroup ↥L :=
    (Ubar ⊓ Subgroup.centralizer ({conjAct L ⟨u, huN⟩} : Set (MulAut ↥L))).comap
      (MulAut.conj : ↥L →* MulAut ↥L)
  let U : Subgroup P := C.map L.subtype
  let U₀ : Subgroup P := C₀.map L.subtype
  have hCmap : C.map (MulAut.conj : ↥L →* MulAut ↥L) = Ubar :=
    Subgroup.map_comap_eq_self hUbar_le
  have hC₀map : C₀.map (MulAut.conj : ↥L →* MulAut ↥L) =
      Ubar ⊓ Subgroup.centralizer ({conjAct L ⟨u, huN⟩} : Set (MulAut ↥L)) :=
    Subgroup.map_comap_eq_self (inf_le_left.trans hUbar_le)
  have hUsub : U.subgroupOf L = C := subgroupOf_map_subtype' C
  have hU₀sub : U₀.subgroupOf L = C₀ := subgroupOf_map_subtype' C₀
  have hUleL : U ≤ L := Subgroup.map_subtype_le C
  have hU₀leU : U₀ ≤ U := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have hCne : C ≠ ⊥ := by
    intro hC
    apply hUbar_ne
    rw [← hCmap, hC, Subgroup.map_bot]
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hCne
    have hmap : C.map L.subtype = (⊥ : Subgroup ↥L).map L.subtype := by
      change U = (⊥ : Subgroup ↥L).map L.subtype
      rw [hU, Subgroup.map_bot]
    exact Subgroup.map_injective L.subtype_injective hmap
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
    have hcommA : (MulAut.conj : ↥L →* MulAut ↥L) a *
        (MulAut.conj : ↥L →* MulAut ↥L) b =
        (MulAut.conj : ↥L →* MulAut ↥L) b *
        (MulAut.conj : ↥L →* MulAut ↥L) a :=
      hUbar_comm _ ha _ hb
    have hab : a * b = b * a := by
      apply conj_injective hZ
      rw [map_mul, map_mul]
      exact hcommA
    calc x * y = (a : P) * (b : P) := by rw [← hax, ← hby]; rfl
      _ = ((a * b : ↥L) : P) := rfl
      _ = ((b * a : ↥L) : P) := by rw [hab]
      _ = (b : P) * (a : P) := rfl
      _ = y * x := by rw [← hby, ← hax]; rfl
  have hUexp : ∀ x ∈ U, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have hpowbar : ((MulAut.conj : ↥L →* MulAut ↥L) a) ^ p = 1 := hUbar_exp _ ha
    have hapow : a ^ p = 1 := by
      apply conj_injective hZ
      rw [map_pow, hpowbar, map_one]
    calc x ^ p = (a : P) ^ p := by rw [← hax]; rfl
      _ = ((a ^ p : ↥L) : P) := (Subgroup.coe_pow L a p).symm
      _ = 1 := by rw [hapow, Subgroup.coe_one]
  have hUnorm : ∀ x ∈ U, u * x * u⁻¹ ∈ U := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    let b : ↥L := ⟨u * (a : P) * u⁻¹,
      (Subgroup.mem_normalizer_iff.mp huN (a : P)).mp a.2⟩
    have hbC : b ∈ C := by
      change (MulAut.conj : ↥L →* MulAut ↥L) b ∈ Ubar
      have hbar : (MulAut.conj : ↥L →* MulAut ↥L) a ∈ Ubar := ha
      have hnorm := hUbar_norm _ hbar
      have hb_eq : (MulAut.conj : ↥L →* MulAut ↥L) b =
          conjAct L ⟨u, huN⟩ * (MulAut.conj : ↥L →* MulAut ↥L) a *
            (conjAct L ⟨u, huN⟩)⁻¹ := by
        simpa [b] using (conjAct_mulAut_conj huN a).symm
      rw [hb_eq]
      exact hnorm
    have hbU : (b : P) ∈ U := Subgroup.mem_map.mpr ⟨b, hbC, rfl⟩
    rw [← hax]
    simpa [b] using hbU
  have hU₀comm : ∀ x ∈ U₀, x * u = u * x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have haC : (MulAut.conj : ↥L →* MulAut ↥L) a ∈
        Ubar ⊓ Subgroup.centralizer ({conjAct L ⟨u, huN⟩} : Set (MulAut ↥L)) :=
      Subgroup.mem_comap.mp ha
    have hcommA : (MulAut.conj : ↥L →* MulAut ↥L) a * conjAct L ⟨u, huN⟩ =
        conjAct L ⟨u, huN⟩ * (MulAut.conj : ↥L →* MulAut ↥L) a :=
      Subgroup.mem_centralizer_singleton_iff.mp haC.2
    have huQE : u ∈ QE t u := Subgroup.subset_closure (by simp)
    have hGN : QG L t u ≤ normalizer (L : Set P) := QG_le_normalizer htN huN
    have haG : (a : P) ∈ QG L t u := L_le_QG a.2
    have hcommImages : liftAlpha hGN ⟨(a : P), haG⟩ * liftAlpha hGN ⟨u, QE_le_QG huQE⟩ =
        liftAlpha hGN ⟨u, QE_le_QG huQE⟩ * liftAlpha hGN ⟨(a : P), haG⟩ := by
      have hαa : liftAlpha hGN ⟨(a : P), haG⟩ = (MulAut.conj : ↥L →* MulAut ↥L) a := by
        show conjAct L ⟨(a : P), hGN haG⟩ = (MulAut.conj : ↥L →* MulAut ↥L) a
        rw [show (⟨(a : P), hGN haG⟩ : normalizer (L : Set P)) =
            ⟨(a : P), Subgroup.le_normalizer a.2⟩ from Subtype.ext rfl]
        exact conjAct_mk_eq_conj a.2
      have hαu : liftAlpha hGN ⟨u, QE_le_QG huQE⟩ = conjAct L ⟨u, huN⟩ := by
        show conjAct L ⟨u, hGN (QE_le_QG huQE)⟩ = conjAct L ⟨u, huN⟩
        exact congrArg (conjAct L) (Subtype.ext rfl)
      rw [hαa, hαu]
      exact hcommA
    have hcomm := commute_of_commute_images htN huN htu hZ hGN haG huQE hcommImages
    rw [← hax]
    exact hcomm
  have hU₀Yu : U₀ ≤ quadY (QG L t u) (QE t u) u := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have haC : (MulAut.conj : ↥L →* MulAut ↥L) a ∈
        Ubar ⊓ Subgroup.centralizer ({conjAct L ⟨u, huN⟩} : Set (MulAut ↥L)) :=
      Subgroup.mem_comap.mp ha
    have huQE : u ∈ QE t u := Subgroup.subset_closure (by simp)
    have hGN : QG L t u ≤ normalizer (L : Set P) := QG_le_normalizer htN huN
    have hmap_u := map_quadY_eq htN huN htu hZ hGN huQE
    have hαx : (MulAut.conj : ↥L →* MulAut ↥L) a ∈
        quadY (QEbar L t u htN huN ⊔ QI L) (QEbar L t u htN huN)
          (conjAct L ⟨u, huN⟩) := by
      simpa [QEbar] using hUbar_cent haC
    have himg : (MulAut.conj : ↥L →* MulAut ↥L) a ∈
        ((quadY (QG L t u) (QE t u) u).subgroupOf (QG L t u)).map (liftAlpha hGN) := by
      rw [hmap_u]
      exact hαx
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp himg
    have haG : (a : P) ∈ QG L t u := L_le_QG a.2
    have hαa : liftAlpha hGN ⟨(a : P), haG⟩ = (MulAut.conj : ↥L →* MulAut ↥L) a := by
      show conjAct L ⟨(a : P), hGN haG⟩ = (MulAut.conj : ↥L →* MulAut ↥L) a
      rw [show (⟨(a : P), hGN haG⟩ : normalizer (L : Set P)) =
          ⟨(a : P), Subgroup.le_normalizer a.2⟩ from Subtype.ext rfl]
      exact conjAct_mk_eq_conj a.2
    let nG : ↥(QG L t u) := (⟨(a : P), haG⟩ : ↥(QG L t u))⁻¹ * y
    have hker : liftAlpha hGN nG = 1 := by
      change liftAlpha hGN ((⟨(a : P), haG⟩ : ↥(QG L t u))⁻¹ * y) = 1
      rw [map_mul, map_inv, hαa, hyeq, inv_mul_cancel]
    have hnN : (nG : P) ∈ QN L t u := by
      have hzC : (nG : P) ∈ Subgroup.centralizer (L : Set P) := by
        have hker' : conjAct L ⟨(nG : P), hGN nG.2⟩ = 1 := by
          show conjAct L (Subgroup.inclusion hGN nG) = 1
          exact hker
        exact (AutOn.conjAct_eq_one_iff _).mp hker'
      exact ⟨nG.2, hzC⟩
    have hnQN : (y : P)⁻¹ * (a : P) ∈ QN L t u := by
      have hinv : (nG : P)⁻¹ ∈ QN L t u := (QN L t u).inv_mem hnN
      simpa [nG, mul_assoc] using hinv
    have hyYu : (y : P) ∈ quadY (QG L t u) (QE t u) u :=
      Subgroup.mem_subgroupOf.mp hy
    have hxsup : (a : P) ∈ quadY (QG L t u) (QE t u) u ⊔ QN L t u := by
      have hsplit : (a : P) = (y : P) * ((y : P)⁻¹ * (a : P)) := by group
      rw [hsplit]
      exact (quadY (QG L t u) (QE t u) u ⊔ QN L t u).mul_mem
        (Subgroup.mem_sup_left hyYu) (Subgroup.mem_sup_right hnQN)
    have hxodd : Odd (orderOf (a : P)) := by
      have hxpow : x ^ p = 1 := hUexp x (hU₀leU hx)
      have hxpow' : (a : P) ^ p = 1 := by
        rw [show (a : P) = x from hax]
        exact hxpow
      exact (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hxpow')
    have hmem := mem_of_odd_of_mem_sup (H := quadY (QG L t u) (QE t u) u)
      (N := QN L t u)
      (fun n hn z hz => centralizes_G_of_mem_QN htN huN htu hZ hGN hn z
        ((sup_le (quadY_le le_sup_left) inf_le_left) hz))
      (fun n hn => sq_one_QN htN huN htt huu htu hZ hn) hxsup hxodd
    rw [← hax]
    exact hmem
  have hhyp : ∀ H : Subgroup P, H ≤ U → H.relIndex U = p → ∃ s ∈ L,
      (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧ ¬ U₀ ≤ H.map (MulAut.conj s).toMonoidHom ∧
      (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj u).toMonoidHom ≠
        H.map (MulAut.conj s).toMonoidHom := by
    intro H hHU hrel
    have hHL : H ≤ L := hHU.trans hUleL
    let Hbar : Subgroup (MulAut ↥L) :=
      (H.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)
    have hHbar_le : Hbar ≤ Ubar := by
      change (H.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) ≤ Ubar
      rw [← hCmap]
      exact Subgroup.map_mono (by
        rw [← hUsub]
        exact Subgroup.subgroupOf_mono L hHU)
    have hHbar_rel : Hbar.relIndex Ubar = p := by
      change ((H.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)).relIndex Ubar = p
      rw [show Ubar = (U.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) from by
        rw [hUsub]
        exact hCmap.symm]
      rw [Subgroup.relIndex_map_map_of_injective _ _ (conj_injective hZ)]
      rw [Subgroup.relIndex_subgroupOf hUleL]
      exact hrel
    obtain ⟨sbar, hsbar, hspres, hnotcent, hnotfix⟩ := hUbar_hyp Hbar hHbar_le hHbar_rel
    obtain ⟨s₁, rfl⟩ := MonoidHom.mem_range.mp hsbar
    refine ⟨(s₁ : P), s₁.2, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
      let b : ↥L := ⟨(s₁ : P) * (a : P) * (s₁ : P)⁻¹,
        L.mul_mem (L.mul_mem s₁.2 a.2) (L.inv_mem s₁.2)⟩
      have hbC : b ∈ C := by
        change (MulAut.conj : ↥L →* MulAut ↥L) b ∈ Ubar
        have hbar : (MulAut.conj : ↥L →* MulAut ↥L) a ∈ Ubar := ha
        have hpres := hspres ((MulAut.conj : ↥L →* MulAut ↥L) a) hbar
        have hb_eq : (MulAut.conj : ↥L →* MulAut ↥L) b =
            (MulAut.conj : ↥L →* MulAut ↥L) s₁ *
              (MulAut.conj : ↥L →* MulAut ↥L) a *
              ((MulAut.conj : ↥L →* MulAut ↥L) s₁)⁻¹ := by
          have hbval : b = s₁ * a * s₁⁻¹ := Subtype.ext rfl
          rw [hbval, map_mul, map_mul, map_inv]
        rw [hb_eq]
        exact hpres
      have hbU : (b : P) ∈ U := Subgroup.mem_map.mpr ⟨b, hbC, rfl⟩
      rw [← hax]
      simpa [b] using hbU
    · intro hle
      apply hnotcent
      have hle_sub : U₀.subgroupOf L ≤
          (H.map (MulAut.conj (s₁ : P)).toMonoidHom).subgroupOf L :=
        Subgroup.subgroupOf_mono L hle
      have hle_map := Subgroup.map_mono (f := (MulAut.conj : ↥L →* MulAut ↥L)) hle_sub
      have hleft : (U₀.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) =
          Ubar ⊓ Subgroup.centralizer ({conjAct L ⟨u, huN⟩} : Set (MulAut ↥L)) := by
        rw [hU₀sub, hC₀map]
      have hright : ((H.map (MulAut.conj (s₁ : P)).toMonoidHom).subgroupOf L).map
          (MulAut.conj : ↥L →* MulAut ↥L) =
          Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom := by
        have h := map_subgroupOf_map_conj (H := H) hHL (Subgroup.le_normalizer s₁.2)
        rw [show (conjAct L ⟨(s₁ : P), Subgroup.le_normalizer s₁.2⟩) =
            (MulAut.conj : ↥L →* MulAut ↥L) s₁ from conjAct_mk_eq_conj s₁.2] at h
        simpa [Hbar] using h
      rw [hleft, hright] at hle_map
      exact hle_map
    · intro heq
      apply hnotfix
      let X : Subgroup P := H.map (MulAut.conj (s₁ : P)).toMonoidHom
      let Y : Subgroup P := X.map (MulAut.conj u).toMonoidHom
      have hXleL : X ≤ L := by
        intro z hz
        obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hz
        exact conj_mem_L (Subgroup.le_normalizer s₁.2) (hHL hh)
      have hYleL : Y ≤ L := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
        exact conj_mem_L huN (hXleL hx)
      have hXbar : (X.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) =
          Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom := by
        have h := map_subgroupOf_map_conj (H := H) hHL (Subgroup.le_normalizer s₁.2)
        rw [show (conjAct L ⟨(s₁ : P), Subgroup.le_normalizer s₁.2⟩) =
            (MulAut.conj : ↥L →* MulAut ↥L) s₁ from conjAct_mk_eq_conj s₁.2] at h
        simpa [X, Hbar] using h
      have hYsub : Y.subgroupOf L = (X.subgroupOf L).map (conjAct L ⟨u, huN⟩) := by
        simpa [Y] using subgroupOf_map_conj (H := X) hXleL huN
      have hYbar : (Y.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) =
          (Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom).map
            (MulAut.conj (conjAct L ⟨u, huN⟩)).toMonoidHom := by
        calc (Y.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)
            = ((X.subgroupOf L).map (conjAct L ⟨u, huN⟩)).map
                (MulAut.conj : ↥L →* MulAut ↥L) := by rw [hYsub]
          _ = ((X.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L)).map
                (MulAut.conj (conjAct L ⟨u, huN⟩)).toMonoidHom :=
              map_conj_mulAut (X.subgroupOf L) (conjAct L ⟨u, huN⟩)
          _ = (Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom).map
                (MulAut.conj (conjAct L ⟨u, huN⟩)).toMonoidHom := by rw [hXbar]
      have hYX : Y = X := by simpa [X, Y] using heq
      have hsub : Y.subgroupOf L = X.subgroupOf L := by rw [hYX]
      have hEqMap : (Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom).map
            (MulAut.conj (conjAct L ⟨u, huN⟩)).toMonoidHom =
          Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom :=
        calc (Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom).map
              (MulAut.conj (conjAct L ⟨u, huN⟩)).toMonoidHom
            = (Y.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) := hYbar.symm
          _ = (X.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) := by rw [hsub]
          _ = Hbar.map (MulAut.conj (MulAut.conj s₁)).toMonoidHom := hXbar
      exact hEqMap
  exact ⟨p, U, U₀, hp, hp2, hUleL, hUne, hUcomm, hUexp, hUnorm, hU₀leU, hU₀comm, hU₀Yu, hhyp⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
