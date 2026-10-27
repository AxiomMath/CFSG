module

public import CFSG.Quasithin.Vol2.Ch11SecO1B
public import CFSG.Quasithin.Vol2.Ch11SecO1C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4G
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGA
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGG
public import CFSG.Quasithin.Vol2.Ch11SecAKC1
public import CFSG.Quasithin.Vol2.Ch11SecEFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem exists_apply_eq_of_faithful {W : Type*} [Group W] [Finite W] {K M : Type} [Field K]
    [AddCommGroup M] [Module K M] {f : W → M} (hfinj : Function.Injective f) {U : Subgroup W}
    (hline : ∀ z ∈ U, z ≠ 1 → ∀ w ∈ U, ∃ c : K, f w = c • f z) {C : Subgroup (MulAut W)}
    (hlin : ∀ d ∈ C, ∃ A : M →ₗ[K] M, ∀ w, f (d w) = A (f w)) (hst : ∀ d ∈ C, ∀ w ∈ U, d w ∈ U)
    (hfaith : ∀ d ∈ C, (∀ w ∈ U, d w = w) → d = 1) (hcard : Nat.card C + 1 = Nat.card U)
    {z : W} (hz : z ∈ U) (hz1 : z ≠ 1) {w : W} (hw : w ∈ U) (hw1 : w ≠ 1) :
    ∃ d ∈ C, d z = w := by
  have hinj : Function.Injective (fun d : ↥C => (⟨(d : MulAut W) z, hst d d.2 z hz⟩ : ↥U)) := by
    intro d d' h
    have h1 : ((d' : MulAut W)⁻¹ * d) z = z := by
      rw [MulAut.mul_apply, show (d : MulAut W) z = (d' : MulAut W) z from congrArg Subtype.val h,
        MulAut.inv_apply_self]
    have hmem : (d' : MulAut W)⁻¹ * d ∈ C := C.mul_mem (C.inv_mem d'.2) d.2
    obtain ⟨A, hA⟩ := hlin _ hmem
    have h2 := hfaith _ hmem fun u hu => by
      obtain ⟨c, hc⟩ := hline z hz hz1 u hu
      apply hfinj
      rw [hA, hc, LinearMap.map_smul, ← hA, h1]
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  set F : Option ↥C → ↥U := fun o => o.elim 1 fun d => ⟨(d : MulAut W) z, hst d d.2 z hz⟩
  have hF1 : ∀ d : ↥C, F (some d) ≠ F none := by
    intro d h
    have h1 : (d : MulAut W) z = 1 := congrArg Subtype.val h
    exact hz1 ((MulEquiv.map_eq_one_iff _).mp h1)
  have hFinj : Function.Injective F := by
    rintro (_ | d) (_ | d') h
    · rfl
    · exact absurd h.symm (hF1 d')
    · exact absurd h (hF1 d)
    · exact congrArg some (hinj h)
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hbij := (Nat.bijective_iff_injective_and_card F).mpr
    ⟨hFinj, by rw [Finite.card_option, hcard]⟩
  obtain ⟨o, ho⟩ := hbij.2 ⟨w, hw⟩
  rcases o with _ | d
  · exact absurd (congrArg Subtype.val ho : (1 : W) = w).symm hw1
  · exact ⟨d, d.2, congrArg Subtype.val ho⟩

variable [Finite G]

theorem line_of_card {L V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    {f : ↥V → M} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hmul : ∀ u u' : ↥V, f (u * u') = f u + f u') (hbij : Function.Bijective f)
    (hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M, ∀ v w : ↥V, (w : G) = l * v * l⁻¹ → f w = A (f v))
    (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {U : Subgroup G} (hUV : U ≤ V)
    (hU : IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U)
    (hcard : Nat.card U = Nat.card K) :
    ∀ z ∈ U.subgroupOf V, z ≠ 1 → ∀ w ∈ U.subgroupOf V, ∃ c : K, f w = c • f z := by
  intro z hz hz1 w hw
  have : Finite M := Finite.of_surjective f hbij.2
  have hz0 : f z ≠ 0 := fun h0 => hz1 (hbij.1 (h0.trans (map_one_of_add hmul).symm))
  have hS := eq_span_of_card ((card_imgSub hLV hmul hbij hlin hC hUV hU).trans hcard)
    ((mem_imgSub_iff hLV hmul hbij hlin hC hU z).mpr hz) hz0
  have h1 := (mem_imgSub_iff hLV hmul hbij hlin hC hU w).mpr hw
  rw [hS, Submodule.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc.symm⟩

variable {T L I : Subgroup G} {n : ℕ}

theorem exists_conj_of_cartanData [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    {D : FFModel} {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]
    {LM : LinModel D K M} (hK : Nat.card K = 2 ^ n) {π : D.Gam →* ↥(autOn L (fsuV T I))}
    {f : ↥(fsuV T I) → M} (hf : IsCoord LM (autOn L (fsuV T I)) ⊥ π f) {V₁ X : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hXL : X ≤ L) {C : Subgroup (MulAut ↥(fsuV T I))}
    (hCX : C ≤ autOn X (fsuV T I))
    (hst : ∀ d ∈ C, ∀ w ∈ V₁.subgroupOf (fsuV T I), d w ∈ V₁.subgroupOf (fsuV T I))
    (hfaith : ∀ d ∈ C, (∀ w ∈ V₁.subgroupOf (fsuV T I), d w = w) → d = 1)
    (hcard : Nat.card C = 2 ^ n - 1) :
    ∀ z ∈ V₁, z ≠ 1 → ∀ w ∈ V₁, w ≠ 1 → ∃ x ∈ X, x * z * x⁻¹ = w := by
  intro z hz hz1 w hw hw1
  have hbij : Function.Bijective f := ⟨IsCoord.injective_of_bot hf, hf.surj⟩
  have hlin : ∀ l ∈ L, ∃ A : M →ₗ[K] M,
      ∀ v w : ↥(fsuV T I), (w : G) = l * v * l⁻¹ → f w = A (f v) :=
    fun l hl => (IsCoord.exists_conj hf hS.le_normalizer hl).elim fun γ hγ => ⟨LM.lin γ, hγ⟩
  obtain ⟨⟨-, hV₁V, hV₁s, hidx, -⟩, -⟩ := hV₁
  have hcardV₁ : Nat.card V₁ = 2 ^ n := by
    rw [hS.cV, Subgroup.relIndex_bot_left, mul_one] at hidx
    exact hidx
  have hline := line_of_card hS.le_normalizer hf.map_mul hbij hlin hS.cV hV₁V hV₁s
    (hcardV₁.trans hK.symm)
  have hcU : Nat.card C + 1 = Nat.card (V₁.subgroupOf (fsuV T I)) := by
    rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁V).toEquiv, hcardV₁]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨d, hdC, hd⟩ := exists_apply_eq_of_faithful hbij.1 hline
    (fun d hd => (hf.exists_lin ⟨d, autOn_mono hXL (hCX hd)⟩).elim fun γ hγ => ⟨LM.lin γ, hγ⟩)
    hst
    hfaith hcU (z := ⟨z, hV₁V hz⟩) hz (fun h => hz1 (congrArg Subtype.val h))
    (w := ⟨w, hV₁V hw⟩) hw (fun h => hw1 (congrArg Subtype.val h))
  obtain ⟨x, hx, hxV, rfl⟩ := SecA.mem_autOn_iff.mp (hCX hdC)
  refine ⟨x, hx, ?_⟩
  have := congrArg Subtype.val hd
  rwa [conjV_apply_coe] at this

theorem faithful_of_cartanPoint {W : Type*} [Group W] {H D : Subgroup (MulAut W)} {U₁ : Subgroup W}
    (h : CartanPoint H ⊥ U₁ D) : ∀ d ∈ centW D (gammaW H U₁), (∀ w ∈ U₁, d w = w) → d = 1 :=
  fun d hd hw => h d hd fun u hu => by
    rw [hw u hu, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecE.cartanPointFact_holds : SecE.CartanPointFact := by
  intro G _ _ T L I n V₁ X hS hV₁ hX
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  have hXL : X ≤ L := fun x hx => (hX.1 hx).1
  have hU₁ := isFlagW_of_isVi hS hV₁
  have hD := isHall_autOn_cartan hS hX
  have hP := isSylowTwoOf_P hS
  have hsq := sq_eq_one hS
  obtain ⟨U₁, U₂, -, -, h₂, -, -, -, hu₁, -, -⟩ := hasUniqueFlag hS
  have hst : ∀ d ∈ centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I))
      (V₁.subgroupOf (fsuV T I))), ∀ w ∈ V₁.subgroupOf (fsuV T I),
        d w ∈ V₁.subgroupOf (fsuV T I) := by
    intro d hd w hw
    have hdD := hD.1 hd.1
    have h1 := mem_stabW_of_mem_normalizer hU₁
      (fun U' hU' => (hu₁ _ hU').trans (hu₁ _ hU₁).symm) hdD.1 hdD.2 (mem_stabW_bot d)
    exact (mem_stabW.mp h1 w).mp hw
  rcases realizes_cases hS with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩
  · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    exact exists_conj_of_cartanData hS hK hf hV₁ hXL inf_le_left hst
      (faithful_of_cartanPoint (factCartanPointSL3_holds K n hn hK _ hsq _ _ π hπ _ hP _ hU₁ _ hD))
      (factCartanSL3_holds K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ h₂ _ hD).2.2.2.2.1
  · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
    exact exists_conj_of_cartanData hS hK hf hV₁ hXL inf_le_left hst
      (faithful_of_cartanPoint (factCartanPointSp4_holds K n hn hK _ hsq _ _ π hπ _ hP _ hU₁ _ hD))
      (factCartanSp4_holds K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ h₂ _ hD).1.2.2.2.2.1
  · have : CharP K 2 := charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := exists_isCoord (linModelZorn _ commutator_quasithinG2_le) hπ
    exact exists_conj_of_cartanData hS hK hf hV₁ hXL inf_le_left hst
      (faithful_of_cartanPoint (factCartanPointG2_holds K n hn hK _ hsq _ _ π hπ _ hP _ hU₁ _ hD))
      (G2Q8.factCartanG2_holds K n hn hK _ hsq _ _ π hπ _ hP _ _ hU₁ h₂ _ hD).1.2.2.2.2.1

end CFSG.Quasithin.Vol2.Ch11.SecO1
