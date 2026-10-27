module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.H13.Ch3Sec3

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem commutator_le_right_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : ⁅A, B⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb) (B.inv_mem hb)

theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_right_of_le_normalizer h

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le_right_of_le_normalizer Subgroup.le_normalizer

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem commutatorElement_mul_right_of_commute {k n b : G} (h : n * b = b * n) :
    ⁅k * n, b⁆ = ⁅k, b⁆ := by
  calc ⁅k * n, b⁆ = k * (n * b) * n⁻¹ * k⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = k * (b * n) * n⁻¹ * k⁻¹ * b⁻¹ := by rw [h]
    _ = ⁅k, b⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_right_of_commute' {k n b : G} (h : n * k⁻¹ = k⁻¹ * n) :
    ⁅k, b * n⁆ = ⁅k, b⁆ := by
  calc ⁅k, b * n⁆ = k * b * (n * k⁻¹) * n⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = k * b * (k⁻¹ * n) * n⁻¹ * b⁻¹ := by rw [h]
    _ = ⁅k, b⁆ := by simp only [commutatorElement_def]; group

theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer (A : Set G) →
      y ∈ Subgroup.normalizer (B : Set G) → ∀ z ∈ A ⊔ B, y * z * y⁻¹ ∈ A ⊔ B := by
    intro y hyA hyB z hz
    have hle : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hyA a).mp ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
    exact hle ⟨z, hz, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key x hA hB z
  · intro hz
    have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hz
    simpa [mul_assoc] using this

theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hA y) (Subgroup.mem_normalizer_iff.mp hB y)

theorem mem_normalizer_commutator {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer (A : Set G) →
      y ∈ Subgroup.normalizer (B : Set G) → ∀ z ∈ ⁅A, B⁆, y * z * y⁻¹ ∈ ⁅A, B⁆ := by
    intro y hyA hyB z hz
    have hle : (⁅A, B⁆).map (MulAut.conj y).toMonoidHom ≤ ⁅A, B⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hyA a).mp ha
      · rintro _ ⟨b, hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
    exact hle ⟨z, hz, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key x hA hB z
  · intro hz
    have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hz
    simpa [mul_assoc] using this

theorem commutator_sup_le_of_le_normalizer {Y Z N : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (hZ : Z ≤ Subgroup.normalizer (N : Set G)) :
    ⁅Y ⊔ N, Z⁆ ≤ ⁅Y, Z⁆ ⊔ N := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have hw' : w ∈ (Y : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y N hY]
    exact hw
  obtain ⟨y, hy, c, hc, rfl⟩ := hw'
  have hcz : ⁅c, z⁆ ∈ N := by
    rw [commutatorElement_def]
    have : z * c⁻¹ * z⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hZ hz) _).mp (inv_mem hc)
    simpa [mul_assoc] using N.mul_mem hc this
  have hycz : y * ⁅c, z⁆ * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hY hy) _).mp hcz
  rw [show ⁅y * c, z⁆ = (y * ⁅c, z⁆ * y⁻¹) * ⁅y, z⁆ by simp only [commutatorElement_def]; group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hycz)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy hz))

theorem conjClosure_sup_eq (L T : Subgroup G) : conjClosure L T ⊔ T = L ⊔ T := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le_sup_right (le_conjClosure L T) T)
  refine conjClosure_le fun t ht l hl => ?_
  exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hl))
    ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))

theorem le_normalizer_conjClosure_right (L T : Subgroup G) :
    T ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
  intro t ht
  have key : ∀ s ∈ T, ∀ x ∈ conjClosure L T, s * x * s⁻¹ ∈ conjClosure L T := by
    intro s hs x hx
    have hle : (conjClosure L T).map (MulAut.conj s).toMonoidHom ≤ conjClosure L T := by
      unfold conjClosure
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨u, hu, l, hl, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨s * u, T.mul_mem hs hu, l, hl, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t ht x
  · intro hx
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

theorem sup_le_normalizer_conjClosure (L T : Subgroup G) :
    L ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
  rw [← conjClosure_sup_eq]
  exact sup_le Subgroup.le_normalizer (le_normalizer_conjClosure_right L T)

theorem commutator_conjClosure_eq {L T : Subgroup G} (hperf : ⁅L, L⁆ = L) :
    ⁅conjClosure L T, conjClosure L T⁆ = conjClosure L T := by
  refine le_antisymm (commutator_self_le _) (conjClosure_le fun t ht l hl => ?_)
  have h2 : L.map (MulAut.conj t).toMonoidHom ≤ conjClosure L T := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.subset_closure ⟨t, ht, y, hy, rfl⟩
  have h1 : (⁅L, L⁆).map (MulAut.conj t).toMonoidHom ≤ ⁅conjClosure L T, conjClosure L T⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono h2 h2
  have hl' : l ∈ ⁅L, L⁆ := hperf.symm ▸ hl
  exact h1 ⟨l, hl', rfl⟩

theorem commutator_conjClosure_le {L T N R H : Subgroup G} (hTH : T ≤ H) (hLH : L ≤ H)
    (hNH : H ≤ Subgroup.normalizer (N : Set G)) (hRH : H ≤ Subgroup.normalizer (R : Set G))
    (h : ⁅L, N⁆ ≤ R) : ⁅conjClosure L T, N⁆ ≤ R := by
  let K : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ n ∈ N, ⁅x, n⁆ ∈ R}
      one_mem' := ⟨H.one_mem, fun n _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨H.mul_mem hxH hyH, fun n hn => ?_⟩
        have e : ⁅x * y, n⁆ = (x * ⁅y, n⁆ * x⁻¹) * ⁅x, n⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRH hxH) _).mp (hy n hn)) (hx n hn)
      inv_mem' := by
        rintro x ⟨hxH, hx⟩
        refine ⟨H.inv_mem hxH, fun n hn => ?_⟩
        have e : ⁅x⁻¹, n⁆ = x⁻¹ * ⁅x, n⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hRH (H.inv_mem hxH)) _).mp (R.inv_mem (hx n hn)) }
  have hK : conjClosure L T ≤ K := by
    refine conjClosure_le fun t ht l hl => ⟨?_, fun n hn => ?_⟩
    · exact H.mul_mem (H.mul_mem (hTH ht) (hLH hl)) (H.inv_mem (hTH ht))
    · have hn' : t⁻¹ * n * t⁻¹⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hNH (H.inv_mem (hTH ht))) n).mp hn
      have hc : ⁅l, t⁻¹ * n * t⁻¹⁻¹⁆ ∈ R := h (Subgroup.commutator_mem_commutator hl hn')
      have e : ⁅t * l * t⁻¹, n⁆ = t * ⁅l, t⁻¹ * n * t⁻¹⁻¹⁆ * t⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hRH (hTH ht)) _).mp hc
  rw [Subgroup.commutator_le]
  intro x hx n hn
  exact (hK hx).2 n hn

theorem le_or_commutator_le_pCoreOf_step {L X' X : Subgroup G} (hLX' : L ≤ X') (hX'X : X' ≤ X)
    (hn : X ≤ Subgroup.normalizer (X' : Set G)) (hperf : ⁅L, L⁆ = L)
    (hP : ∀ N : Subgroup G, N ≤ X' → X' ≤ Subgroup.normalizer (N : Set G) →
      L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 X')
    {N : Subgroup G} (hNX : N ≤ X) (hN : X ≤ Subgroup.normalizer (N : Set G)) :
    L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 X := by
  have hX'N : X' ≤ Subgroup.normalizer ((N ⊓ X' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hN (hX'X hx)) (hn (hX'X hx))
  rcases hP (N ⊓ X') inf_le_right hX'N with h | h
  · exact Or.inl (h.trans inf_le_left)
  · right
    have hX'n : (X'.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hX'X).mpr hn
    have hO : pCoreOf 2 X' ≤ pCoreOf 2 X :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 X' X hX'X hX'n
    have hLN : ⁅L, N⁆ ≤ N ⊓ X' := le_inf
      (commutator_le_right_of_le_normalizer ((hLX'.trans hX'X).trans hN))
      ((Subgroup.commutator_mono hLX' le_rfl).trans
        (commutator_le_left_of_le_normalizer (hNX.trans hn)))
    have h1 : ⁅⁅L, N⁆, L⁆ ≤ pCoreOf 2 X :=
      calc ⁅⁅L, N⁆, L⁆ ≤ ⁅N ⊓ X', L⁆ := Subgroup.commutator_mono hLN le_rfl
        _ = ⁅L, N ⊓ X'⁆ := Subgroup.commutator_comm _ _
        _ ≤ pCoreOf 2 X' := h
        _ ≤ pCoreOf 2 X := hO
    have h2 : ⁅⁅N, L⁆, L⁆ ≤ pCoreOf 2 X := by
      rw [Subgroup.commutator_comm N L]
      exact h1
    have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      (hLX'.trans hX'X).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have hNO : N ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hNX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have h3 := three_subgroups_mod hLO hNO hLO h1 h2
    rwa [hperf] at h3

variable [Finite G]

theorem exists_centralizer_mem_coset {H T V W : Subgroup G}
    (hodd : ¬ 2 ∣ T.relIndex H) (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hHW : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ * v⁻¹ ∈ W)
    {z : G} (hzV : z ∈ V) (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ c ∈ V, (∀ h ∈ H, h * c * h⁻¹ = c) ∧ c * z⁻¹ ∈ W := by
  classical
  have hcomm : IsMulCommutative ↥V := hV.1
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm a.2 b.2) }
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  let _ : Fintype (↥H ⧸ T') := Fintype.ofFinite _
  have hconj : ∀ g : G, g ∈ H → ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hHV hg) v).mp hv
  let F : ↥H ⧸ T' → ↥V := fun q =>
    ⟨((q.out : ↥H) : G) * z * ((q.out : ↥H) : G)⁻¹, hconj _ q.out.2 z hzV⟩
  set c : ↥V := ∏ q, F q with hc
  refine ⟨c, c.2, ?_, ?_⟩
  · intro h hh
    let φ : ↥V →* ↥V :=
      { toFun := fun v => ⟨h * v * h⁻¹, hconj h hh v v.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group }
    have hφ : ∀ q, φ (F q) = F ((⟨h, hh⟩ : ↥H) • q) := by
      intro q
      apply Subtype.ext
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T' ((⟨h, hh⟩ : ↥H) * q.out)
      have hq : (QuotientGroup.mk ((⟨h, hh⟩ : ↥H) * q.out) : ↥H ⧸ T') = (⟨h, hh⟩ : ↥H) • q :=
        MulAction.Quotient.mk_smul_out T' (⟨h, hh⟩ : ↥H) q
      rw [hq] at ht
      have htT : ((t : ↥H) : G) ∈ T := Subgroup.mem_subgroupOf.mp t.2
      have hval : (((⟨h, hh⟩ : ↥H) • q).out : G) = h * (q.out : G) * ((t : ↥H) : G) := by
        rw [ht]
        rfl
      have htz : ((t : ↥H) : G) * z * ((t : ↥H) : G)⁻¹ = z := by
        rw [hzT _ htT]
        group
      show h * ((q.out : G) * z * (q.out : G)⁻¹) * h⁻¹ =
        (((⟨h, hh⟩ : ↥H) • q).out : G) * z * (((⟨h, hh⟩ : ↥H) • q).out : G)⁻¹
      rw [hval]
      calc h * ((q.out : G) * z * (q.out : G)⁻¹) * h⁻¹
          = h * (q.out : G) * (((t : ↥H) : G) * z * ((t : ↥H) : G)⁻¹) * (q.out : G)⁻¹ * h⁻¹ := by
            rw [htz]; group
        _ = h * (q.out : G) * ((t : ↥H) : G) * z * (h * (q.out : G) * ((t : ↥H) : G))⁻¹ := by
            group
    have hfix : φ c = c := by
      rw [hc, map_prod]
      simp_rw [hφ]
      exact Fintype.prod_equiv (MulAction.toPerm (⟨h, hh⟩ : ↥H)) _ _ (fun q => rfl)
    exact congrArg Subtype.val hfix
  · set z' : ↥V := ⟨z, hzV⟩ with hz'
    have hW' : ∀ q, F q * z'⁻¹ ∈ W.subgroupOf V := by
      intro q
      rw [Subgroup.mem_subgroupOf]
      exact hHW _ q.out.2 z hzV
    have hprod : ∏ q, (F q * z'⁻¹) ∈ W.subgroupOf V :=
      Subgroup.prod_mem _ fun q _ => hW' q
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← hc] at hprod
    have hn : Odd (Finset.univ : Finset (↥H ⧸ T')).card := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    obtain ⟨k, hk⟩ := hn
    have hz2 : z' * z' = 1 := Subtype.ext (by
      have := hV.2 z hzV
      simpa [pow_two] using this)
    have hpow : z'⁻¹ ^ (Finset.univ : Finset (↥H ⧸ T')).card = z'⁻¹ := by
      rw [hk, pow_succ, pow_mul, inv_pow, sq, hz2, inv_one, one_pow, one_mul]
    rw [hpow] at hprod
    exact Subgroup.mem_subgroupOf.mp hprod

theorem le_of_isPGroup_quotient {L N : Subgroup G} (hperf : ⁅L, L⁆ = L)
    [hNL : (N.subgroupOf L).Normal] (h2 : IsPGroup 2 (↥L ⧸ N.subgroupOf L)) : L ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (↥L ⧸ N.subgroupOf L) := h2.isNilpotent
  have hL : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hperf]
  have hQ : commutator (↥L ⧸ N.subgroupOf L) = ⊤ := by
    have hs := QuotientGroup.mk'_surjective (N.subgroupOf L)
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator,
      ← commutator_def, hL]
  have hsub : Subsingleton (↥L ⧸ N.subgroupOf L) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L ⧸ N.subgroupOf L)).ne hQ
  intro x hx
  have h1 : (QuotientGroup.mk' (N.subgroupOf L) ⟨x, hx⟩ : ↥L ⧸ N.subgroupOf L) = 1 :=
    Subsingleton.elim _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem le_or_commutator_le_pCoreOf_self {L N : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L)) (hperf : ⁅L, L⁆ = L)
    (hNL : N ≤ L) (hN : L ≤ Subgroup.normalizer (N : Set G)) :
    L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCore 2 ↥L with hP
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hN'n : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hN
  set K : Subgroup (↥L ⧸ P) := (N.subgroupOf L).map (QuotientGroup.mk' P) with hK
  have hKn : K.Normal := hN'n.map (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq K with hc | ht
  · right
    rw [Subgroup.commutator_le]
    intro l hl n hn
    have hn' : (⟨n, hNL hn⟩ : ↥L) ∈ N.subgroupOf L := Subgroup.mem_subgroupOf.mpr hn
    have hcen := hc (Subgroup.mem_map_of_mem (QuotientGroup.mk' P) hn')
    have h1 : (QuotientGroup.mk' P) ⁅(⟨l, hl⟩ : ↥L), ⟨n, hNL hn⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk' P ⟨l, hl⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  · left
    refine le_of_isPGroup_quotient hperf fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf L) q
    have hx : QuotientGroup.mk' P x ∈ K := by rw [ht]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
    have hp : n⁻¹ * x ∈ P := QuotientGroup.eq.mp hnx
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2 ⟨n⁻¹ * x, hp⟩
    refine ⟨k, ?_⟩
    have hk' : (n⁻¹ * x) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hn1 : QuotientGroup.mk' (N.subgroupOf L) n⁻¹ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((N.subgroupOf L).inv_mem hn)
    have e : QuotientGroup.mk' (N.subgroupOf L) x =
        QuotientGroup.mk' (N.subgroupOf L) (n⁻¹ * x) := by
      rw [map_mul, hn1, one_mul]
    rw [e, ← map_pow, hk', map_one]

theorem le_or_commutator_le_pCoreOf {L X : Subgroup G} (hsub : IsSubnormal L X)
    (hperf : ⁅L, L⁆ = L) (hq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L))
    {N : Subgroup G} (hNX : N ≤ X) (hN : X ≤ Subgroup.normalizer (N : Set G)) :
    L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 X := by
  have key : ∀ {H K : Subgroup G}, IsSubnormal H K → L ≤ H →
      (∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) →
        L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 H) →
      ∀ N : Subgroup G, N ≤ K → K ≤ Subgroup.normalizer (N : Set G) →
        L ≤ N ∨ ⁅L, N⁆ ≤ pCoreOf 2 K := by
    intro H K h
    induction h with
    | refl => exact fun _ hP => hP
    | step hHM hHn _ ih =>
      intro hLH hP
      exact ih (hLH.trans hHM) fun N hNM hN =>
        le_or_commutator_le_pCoreOf_step hLH hHM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHn) hperf hP hNM hN
  exact key hsub le_rfl (fun N hNL hN => le_or_commutator_le_pCoreOf_self hq hperf hNL hN) N
    hNX hN

theorem le_frattini_of_central {Q : Type} [Group Q] {M N : Subgroup Q} [N.Normal]
    (hNM : N ≤ M) (hM : ⁅M, M⁆ = M) (hc : ⁅M, N⁆ = ⊥) : N ≤ frattini Q := by
  unfold frattini Order.radical
  refine le_iInf₂ fun K hK => ?_
  by_contra hNK
  have hsup : K ⊔ N = ⊤ :=
    hK.2 _ (lt_of_le_of_ne le_sup_left fun h => hNK (h ▸ le_sup_right))
  have hcomm : ∀ m ∈ M, ∀ n ∈ N, n * m = m * n := by
    intro m hm n hn
    have h1 : ⁅m, n⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hm hn
      rw [hc] at this
      exact Subgroup.mem_bot.mp this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hMK : M ≤ K := by
    rw [← hM, Subgroup.commutator_le]
    intro a ha b hb
    have ha' : a ∈ K ⊔ N := hsup ▸ Subgroup.mem_top a
    have hb' : b ∈ K ⊔ N := hsup ▸ Subgroup.mem_top b
    obtain ⟨k₁, hk₁, n₁, hn₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha'
    obtain ⟨k₂, hk₂, n₂, hn₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb'
    have hk₁M : k₁ ∈ M := by
      have := M.mul_mem ha (M.inv_mem (hNM hn₁))
      simpa using this
    rw [commutatorElement_mul_right_of_commute (hcomm _ hb n₁ hn₁),
      commutatorElement_mul_right_of_commute' (hcomm _ (M.inv_mem hk₁M) n₂ hn₂),
      commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  exact hNK (hNM.trans hMK)

theorem centralizer_reduced_of_cComp {L T V : Subgroup G} (hLc : L ∈ cComp (L ⊔ T))
    (hq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L)) (hT : IsSylowTwoOf T (L ⊔ T))
    (hV : IsTwoReducedIn (L ⊔ T) V) (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    ⁅conjClosure L T, (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)⁆ ≤ pCoreOf 2 (L ⊔ T) ∧
      T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) ∧
      (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := L ⊔ T with hH
  set N := H ⊓ Subgroup.centralizer (V : Set G) with hNdef
  set R := pCoreOf 2 H with hR
  set M₀ := conjClosure L T with hM₀
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hLH : L ≤ H := le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  have hNH : N ≤ H := inf_le_left
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx)
      (B2F.normalizer_le_normalizer_centralizer V (hHV hx))
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hM₀H : M₀ ≤ H := by
    rw [hH, ← conjClosure_sup_eq]
    exact le_sup_left
  have hHM₀ : H ≤ Subgroup.normalizer (M₀ : Set G) := sup_le_normalizer_conjClosure L T
  have h1 : ⁅M₀, N⁆ ≤ R := by
    rcases le_or_commutator_le_pCoreOf (subnormal_of_mem_cComp hLc) hperf hq hNH hHN with
      hle | hle
    · exact absurd (hle.trans inf_le_right) hLV
    · exact commutator_conjClosure_le hTH hLH hHN hHR hle
  have hRT : R ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  have hRV : R ≤ Subgroup.centralizer (V : Set G) := pCoreOf_le_centralizer_of_isTwoReducedIn hV
  have h2 : T ⊓ Subgroup.centralizer (V : Set G) = R := by
    refine le_antisymm ?_ (le_inf hRT hRV)
    set P := T ⊓ Subgroup.centralizer (V : Set G) with hPdef
    have hPH : P ≤ H := inf_le_left.trans hTH
    have hP2 : IsPGroup 2 P := hT.2.1.to_inf_left
    have hRP : R ≤ P := le_inf hRT hRV
    have hM₀P : ∀ m ∈ M₀, ∀ p ∈ P, m * p * m⁻¹ ∈ P := by
      intro m hm p hp
      have hpN : p ∈ N := ⟨hPH hp, hp.2⟩
      have hc : ⁅m, p⁆ ∈ R := h1 (Subgroup.commutator_mem_commutator hm hpN)
      have e : m * p * m⁻¹ = ⁅m, p⁆ * p := by simp only [commutatorElement_def]; group
      rw [e]
      exact P.mul_mem (hRP hc) hp
    have hTP : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
      mem_normalizer_inf (Subgroup.le_normalizer ht)
        (B2F.normalizer_le_normalizer_centralizer V (hHV (hTH ht)))
    have hM₀N : M₀ ≤ Subgroup.normalizer (P : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · exact hM₀P m hm p
      · intro hp
        have := hM₀P m⁻¹ (M₀.inv_mem hm) _ hp
        simpa [mul_assoc] using this
    have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
      rw [hH, ← conjClosure_sup_eq]
      exact sup_le hM₀N hTP
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPH hHP hP2
  refine ⟨h1, h2, ?_⟩
  set A := M₀ ⊔ R with hA
  have hHA : H ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
    mem_normalizer_sup (hHM₀ hx) (hHR hx)
  have hAH : A ≤ H := sup_le hM₀H (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hNA : N ≤ A := by
    have hS : IsSylowTwoOf (T ⊓ N) N := A4.isSylowTwoOf_inf_normal hT hNH hHN
    have hTNA : T ⊓ N ≤ A ⊓ N := by
      refine le_inf ?_ inf_le_right
      have : T ⊓ N ≤ R := by
        rw [← h2]
        exact inf_le_inf_left T inf_le_right
      exact this.trans le_sup_right
    have hodd : ¬ 2 ∣ (A ⊓ N).relIndex N := fun h =>
      hS.2.2 (h.trans (Subgroup.relIndex_dvd_of_le_left N hTNA))
    have hHTA : H = T ⊔ A := by
      refine le_antisymm ?_ (sup_le hTH hAH)
      rw [hH, ← conjClosure_sup_eq]
      exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
    have e1 : (A ⊓ N).relIndex N = A.relIndex N := Subgroup.inf_relIndex_right A N
    have e2 : A.relIndex (N ⊔ A) = A.relIndex N :=
      B2F.relIndex_sup_eq_of_le_normalizer' (hNH.trans hHA)
    have e3 : A.relIndex (T ⊔ A) = A.relIndex T :=
      B2F.relIndex_sup_eq_of_le_normalizer' (hTH.trans hHA)
    have hd1 : A.relIndex (N ⊔ A) ∣ A.relIndex (T ⊔ A) := by
      rw [← hHTA]
      exact Dvd.intro _
        (Subgroup.relIndex_mul_relIndex A (N ⊔ A) H le_sup_right (sup_le hNH hAH))
    have hd2 : A.relIndex T ∣ Nat.card T := by
      rw [← Subgroup.inf_relIndex_right A T]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT.2.1
    have hdvd : (A ⊓ N).relIndex N ∣ 2 ^ k := by
      rw [e1, ← e2, ← hk]
      exact hd1.trans (e3 ▸ hd2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · exact absurd (hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) hodd
    rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hj.trans inf_le_left
  set P₂ := CFSG.Open.pCore 2 ↥H with hP₂
  have : P₂.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π := QuotientGroup.mk' P₂ with hπ
  have hπR : ∀ r ∈ R, ∀ hr : r ∈ H, π ⟨r, hr⟩ = 1 := by
    intro r hrR hr
    obtain ⟨r', hr', rfl⟩ := hrR
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hr'
  set Nq := (N.subgroupOf H).map π with hNq
  set Mq := (M₀.subgroupOf H).map π with hMq
  have hN'n : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have : Nq.Normal := hN'n.map π (QuotientGroup.mk'_surjective P₂)
  have hNqMq : Nq ≤ Mq := by
    rintro _ ⟨⟨x, hxH⟩, hx, rfl⟩
    have hxA : x ∈ A := hNA (Subgroup.mem_subgroupOf.mp hx)
    have hxA' : x ∈ (M₀ : Set G) * (R : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right M₀ R (hM₀H.trans hHR)]
      exact hxA
    obtain ⟨m, hm, r, hr, hmr⟩ := hxA'
    have hmH : m ∈ H := hM₀H hm
    have hrH : r ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hr
    have e : (⟨x, hxH⟩ : ↥H) = ⟨m, hmH⟩ * ⟨r, hrH⟩ := Subtype.ext hmr.symm
    refine ⟨⟨m, hmH⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    rw [e, map_mul, hπR r hr hrH, mul_one]
  have hcomm : ⁅Mq, Nq⁆ = ⊥ := by
    rw [hMq, hNq, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    rintro ⟨x, hxH⟩ hx
    have hx' : x ∈ ⁅M₀, N⁆ := by
      have := Subgroup.mem_map_of_mem H.subtype hx
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM₀H,
        Subgroup.map_subgroupOf_eq_of_le hNH] at this
    rw [MonoidHom.mem_ker]
    exact hπR x (h1 hx') hxH
  have hperfM : ⁅Mq, Mq⁆ = Mq := by
    have hM₀p := commutator_conjClosure_eq (T := T) hperf
    have hsub : ⁅M₀.subgroupOf H, M₀.subgroupOf H⁆ = M₀.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hM₀H]
      exact hM₀p
    rw [hMq, ← Subgroup.map_commutator, hsub]
  have hΦ : Nq ≤ frattini (↥H ⧸ P₂) := le_frattini_of_central hNqMq hperfM hcomm
  intro x hxN
  have hxH : x ∈ H := hNH hxN
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  exact hΦ ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩

end CFSG.Quasithin.H13.Ch3Sec3
