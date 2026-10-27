module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APair
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem c23a_o2_mQuot_eq_rk_sub {V U : Subgroup G} (hUV : U ≤ V) :
    E3.mQuot V U = rk ↥V - rk ↥U := by
  have h1 := rk_add_rkIdx (U.subgroupOf V)
  have h2 : rk ↥(U.subgroupOf V) = rk ↥U := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv]
  have h3 : rkIdx (U.subgroupOf V) = E3.mQuot V U := (E3.mQuot_eq_rkIdx V U).symm
  rw [h2, h3] at h1
  omega

private theorem c23a_o2_mQuot_inf_right (V U : Subgroup G) :
    E3.mQuot V (U ⊓ V) = E3.mQuot V U := by
  unfold E3.mQuot
  rw [Subgroup.inf_relIndex_right]

theorem c23a_o2_mQuot_inf_left (V U : Subgroup G) :
    E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
  rw [inf_comm, c23a_o2_mQuot_inf_right]

private theorem c23a_o2_mem_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (z : G) :
    z ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = z := by
  constructor
  · intro h
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro w (hw | hw)
      · exact ⟨w, hw, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, w, hw, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [hcomm y₂ hy₂ z₁ hz₁]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
      simpa [mul_inv_rev] using (congrArg Inv.inv (hcomm y hy z hz)).symm
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

private theorem c23a_o2_card_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun p => ⟨p.1.1 * p.2.1, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := (c23a_o2_mem_sup_of_comm hcomm z.1).mp z.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hinj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ h
    have h' : h₁.1 * k₁.1 = h₂.1 * k₂.1 := congrArg Subtype.val h
    have hkey : h₁.1⁻¹ * h₂.1 = k₁.1 * k₂.1⁻¹ := by
      calc h₁.1⁻¹ * h₂.1 = h₁.1⁻¹ * (h₂.1 * k₂.1) * k₂.1⁻¹ := by group
        _ = h₁.1⁻¹ * (h₁.1 * k₁.1) * k₂.1⁻¹ := by rw [← h']
        _ = k₁.1 * k₂.1⁻¹ := by group
    have hmem : h₁.1⁻¹ * h₂.1 ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem h₁.2) h₂.2, hkey ▸ K.mul_mem k₁.2 (K.inv_mem k₂.2)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      rwa [inv_mul_eq_one] at hmem
    have hk : k₁ = k₂ := by
      apply Subtype.ext
      rw [hh] at h'
      exact mul_left_cancel h'
    exact Prod.ext hh hk
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

theorem c23a_o2_rk_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hinf : H ⊓ K = ⊥) :
    rk ↥(H ⊔ K) = rk ↥H + rk ↥K := by
  unfold rk
  rw [c23a_o2_card_sup_of_comm hcomm hinf, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']

theorem c23a_o2_comm_mem_inf {M V W W' : Subgroup G} {g : G}
    (hP : C23APair M V W W')
    (hP' : C23APair (conjSubgroup M g) (conjSubgroup V g) (conjSubgroup W g)
      (conjSubgroup W' g))
    {u y : G} (hu : u ∈ V ⊓ conjSubgroup M g) (hy : y ∈ conjSubgroup V g ⊓ M) :
    u * y * u⁻¹ * y⁻¹ ∈ V ⊓ conjSubgroup V g := by
  have huV : u ∈ V := (Subgroup.mem_inf.1 hu).1
  have huMg : u ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hu).2
  have hyVg : y ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hy).1
  have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).2
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hyN : y ∈ normalizer (V : Set G) := hP.norm hyM
    have hmem : y * u⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hyN u⁻¹).1 (V.inv_mem huV)
    have h2 : u * (y * u⁻¹ * y⁻¹) ∈ V := V.mul_mem huV hmem
    simpa only [mul_assoc] using h2
  · have huN : u ∈ normalizer (conjSubgroup V g : Set G) := hP'.norm huMg
    have hmem : u * y * u⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 huN y).1 hyVg
    exact (conjSubgroup V g).mul_mem hmem ((conjSubgroup V g).inv_mem hyVg)

theorem c23a_o2_not_le_centralizer_singleton {X : Subgroup G} {t : G}
    (h : t ∉ centralizer (X : Set G)) : ¬ X ≤ centralizer ({t} : Set G) := by
  intro hle
  refine h ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxt : x ∈ centralizer ({t} : Set G) := hle hx
  rw [Subgroup.mem_centralizer_iff] at hxt
  exact (hxt t rfl).symm

theorem c23a_o2_mem_centralizer_of_swap {V W W' X' Y' : Subgroup G} {a u : G}
    (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hsup : W ⊔ W' = V) (huax : u * a * u⁻¹ = a)
    (hXY : (X' = W ∧ Y' = W') ∨ (X' = W' ∧ Y' = W))
    (hswap : conjSubgroup W u = W' ∧ conjSubgroup W' u = W)
    (hcentY : ∀ y ∈ Y', a * y = y * a) :
    a ∈ centralizer (V : Set G) := by
  have hswapY : conjSubgroup Y' u = X' := by
    rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · rw [hY, hX]; exact hswap.2
    · rw [hY, hX]; exact hswap.1
  have hsup' : X' ⊔ Y' = V := by
    rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · rw [hX, hY]; exact hsup
    · rw [hX, hY, sup_comm]; exact hsup
  have hcommXY : ∀ x ∈ X', ∀ y ∈ Y', x * y = y * x :=
    fun x hx y hy =>
      hVcomm x (hsup' ▸ Subgroup.mem_sup_left hx) y (hsup' ▸ Subgroup.mem_sup_right hy)
  have huaxinv : u * a⁻¹ * u⁻¹ = a⁻¹ := by
    have := congrArg Inv.inv huax
    simpa [mul_inv_rev, mul_assoc] using this
  have hcentX : ∀ x ∈ X', a * x = x * a := by
    intro x hx
    have hwx : u * x * u⁻¹ ∈ Y' :=
      mem_conjSubgroup_iff.1 (by rw [hswapY]; exact hx)
    have haw : a * (u * x * u⁻¹) * a⁻¹ = u * x * u⁻¹ := by
      rw [hcentY (u * x * u⁻¹) hwx]; group
    have hconj : u * (a * x * a⁻¹) * u⁻¹ = u * x * u⁻¹ := by
      calc u * (a * x * a⁻¹) * u⁻¹
          = (u * a * u⁻¹) * (u * x * u⁻¹) * (u * a⁻¹ * u⁻¹) := by group
        _ = a * (u * x * u⁻¹) * a⁻¹ := by rw [huax, huaxinv]
        _ = u * x * u⁻¹ := haw
    have key : a * x * a⁻¹ = x := by
      have h2 : (a * x * a⁻¹) * u⁻¹ = x * u⁻¹ := by
        apply mul_left_cancel (a := u)
        simpa [mul_assoc] using hconj
      exact mul_right_cancel h2
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [key]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : v ∈ X' ⊔ Y' := by rw [hsup']; exact hv
  obtain ⟨x, hx, y, hy, rfl⟩ := (c23a_o2_mem_sup_of_comm hcommXY v).mp hv'
  exact (calc a * (x * y) = (a * x) * y := by group
    _ = (x * a) * y := by rw [hcentX x hx]
    _ = x * (a * y) := by group
    _ = x * (y * a) := by rw [hcentY y hy]
    _ = (x * y) * a := by group).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
