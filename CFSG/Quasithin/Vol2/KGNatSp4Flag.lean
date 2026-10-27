module

public import CFSG.Quasithin.Vol2.KGNatSp4Std
public import CFSG.Quasithin.Vol2.KGNatSL3Flag

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem mat_mulVec_inv (g : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K g *ᵥ (mat 2 K g⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem mat_inv_mulVec (g : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K g⁻¹ *ᵥ (mat 2 K g *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

@[expose] noncomputable def gmapSp (g : StatedSp 2 K) (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  S.map (Matrix.toLin' (mat 2 K g))

theorem mem_gmapSp {g : StatedSp 2 K} {S : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    {x : Fin 2 ⊕ Fin 2 → K} : x ∈ gmapSp g S ↔ mat 2 K g⁻¹ *ᵥ x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.toLin'_apply, mat_inv_mulVec]
    exact hy
  · intro hx
    exact ⟨_, hx, by rw [Matrix.toLin'_apply, mat_mulVec_inv]⟩

theorem card_gmapSp (g : StatedSp 2 K) (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Nat.card (gmapSp g S) = Nat.card S := by
  have hinj : Function.Injective (Matrix.toLin' (mat 2 K g)) := fun x y h => by
    have := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h
    simp only [Matrix.toLin'_apply, mat_inv_mulVec] at this
    exact this
  exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj S).toEquiv.symm

theorem gmapSp_gmapSp_inv (g : StatedSp 2 K) (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    gmapSp g (gmapSp g⁻¹ S) = S := by
  ext x
  rw [mem_gmapSp, mem_gmapSp, inv_inv, mat_mulVec_inv]

theorem gmapSp_mono (g : StatedSp 2 K) {S T : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h : S ≤ T) :
    gmapSp g S ≤ gmapSp g T :=
  Submodule.map_mono h

theorem UStableSp.mem_iff {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S)
    {u : StatedSp 2 K} (hu : u ∈ Usp K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K u *ᵥ x ∈ S ↔ x ∈ S := by
  refine ⟨fun h => ?_, fun h => hS u hu x h⟩
  have := hS u⁻¹ ((Usp K).inv_mem hu) _ h
  rwa [mat_inv_mulVec] at this

theorem conj_mulVec_sp (g u : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K g⁻¹ *ᵥ (mat 2 K (g * u * g⁻¹) *ᵥ x) = mat 2 K u *ᵥ (mat 2 K g⁻¹ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
    show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem IsCoord.act4 (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (γ : StatedSp 2 K)
    (w : W) : f (((π γ : ↥H) : MulAut W) w) = mat 2 K γ *ᵥ f w :=
  (hf.act γ w).trans (linModelNat_lin _ γ _)

theorem IsCoord.pi_mem_stabW_iff_sp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {U : Subgroup W} (hZU : Z ≤ U) (γ : StatedSp 2 K) :
    ((π γ : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U ↔
      ∀ y, y ∈ hf.img U ↔ mat 2 K γ *ᵥ y ∈ hf.img U := by
  refine (hf.mem_stabW_iff hZU γ).trans (forall_congr' fun y => ?_)
  rw [linModelNat_lin]
  rfl

theorem exists_sylow_eq_conj_Usp [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {P : Subgroup (MulAut W)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) :
    ∃ g : StatedSp 2 K, ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, hP2, hPi⟩ := hP
  have hinj : Function.Injective π := hf.injective_nat
  have hsurj : Function.Surjective π := hf.onto
  have hQ2 := isPGroup_comap π hinj hP2
  have hQi : ¬ 2 ∣ ((P.subgroupOf H).comap π).index := by
    rw [index_comap π hsurj]
    exact hPi
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
    (IsPGroup.toSylow (isPGroup_Usp hK) (not_dvd_index_Usp hK (by omega))) (hQ2.toSylow hQi)
  refine ⟨g, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := hsurj ⟨x, hPH hx⟩
    have hAQ : A ∈ (P.subgroupOf H).comap π := by
      rw [Subgroup.mem_comap, hA, Subgroup.mem_subgroupOf]
      exact hx
    rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hAQ
    refine ⟨g⁻¹ * A * g, hAQ, ?_⟩
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
  · rintro ⟨u, hu, rfl⟩
    have hmem : g * u * g⁻¹ ∈ (P.subgroupOf H).comap π := by
      rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem isFlagW_pre_sp (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : StatedSp 2 K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S) {i : ℕ}
    (hcard : Nat.card S = Nat.card K ^ i) :
    Ch11.SecA.IsFlagW H P Z (Nat.card K) i (hf.pre (gmapSp g S).toAddSubgroup) := by
  refine ⟨hf.le_pre _, ?_, ?_, fun x hx => ?_⟩
  · rw [hf.endStableW_iff hW (fun T hT => commutant_statedSp T hT) (hf.le_pre _), hf.img_pre]
    exact fun c x hx => (gmapSp g S).smul_mem c hx
  · rw [← hf.card_img, hf.img_pre, ← hcard, ← card_gmapSp g S]
    rfl
  · obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [hf.pi_mem_stabW_iff_sp (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmapSp g S ↔ _ ∈ gmapSp g S
    rw [mem_gmapSp, mem_gmapSp, conj_mulVec_sp, hS.mem_iff hu]

theorem exists_eq_pre_of_isFlagW_sp (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : StatedSp 2 K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    {i : ℕ} {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) i U) :
    ∃ S : Submodule K (Fin 2 ⊕ Fin 2 → K), UStableSp S ∧ Nat.card S = Nat.card K ^ i ∧
      U = hf.pre (gmapSp g S).toAddSubgroup := by
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  have hsc := (hf.endStableW_iff hW (fun T hT => commutant_statedSp T hT) hZU).mp hst
  let T : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    { carrier := hf.img U
      add_mem' := (hf.img U).add_mem
      zero_mem' := (hf.img U).zero_mem
      smul_mem' := fun c x hx => hsc c x hx }
  have hTcard : Nat.card T = Nat.card K ^ i := by
    rw [← hidx, ← hf.card_img]
    rfl
  refine ⟨gmapSp g⁻¹ T, fun u hu x hx => ?_, by rw [card_gmapSp, hTcard], ?_⟩
  · rw [mem_gmapSp, inv_inv] at hx ⊢
    have hp : ((π (g * u * g⁻¹) : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U :=
      hPU ((hg _).mpr ⟨u, hu, rfl⟩)
    have h1 := ((hf.pi_mem_stabW_iff_sp hZU _).mp hp _).mp hx
    change _ ∈ T at h1
    rw [Matrix.mulVec_mulVec, ← map_mul, show g * u * g⁻¹ * g = g * u by group, map_mul,
      ← Matrix.mulVec_mulVec] at h1
    exact h1
  · rw [gmapSp_gmapSp_inv]
    exact (hf.pre_img hZU).symm

end Real

theorem factFlagSp4_holds : Ch11.SecA.FactFlagSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK]
  refine ⟨_, _, _, isFlagW_pre_sp hW hf hg spLine_stable (by rw [card_spLine, pow_one]),
    isFlagW_pre_sp hW hf hg spPlane_stable card_spPlane,
    isFlagW_pre_sp hW hf hg spHyp_stable card_spHyp,
    fun w hw => gmapSp_mono g spLine_le_spPlane hw,
    fun w hw => gmapSp_mono g spPlane_le_spHyp hw, fun U hU => ?_, fun U hU => ?_,
    fun U hU => ?_⟩
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU
    rw [(eq_std_of_stable_sp hS).1 (by rw [hc, pow_one])]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU
    rw [(eq_std_of_stable_sp hS).2.1 hc]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU
    rw [(eq_std_of_stable_sp hS).2.2 hc]

end CFSG.Quasithin.Vol2.KGNat
