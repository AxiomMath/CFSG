module

public import CFSG.Quasithin.Background.RonanF918FiveIii

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement Matrix

@[expose] noncomputable def multiNatModelU (n m : ℕ) (F : Type) [Field F] : FFModel where
  Gam := ↥(StatedSL n F)
  Amb := Multiplicative (Matrix (Fin n) (Fin m) F)
  act g X := Multiplicative.ofAdd
    (((g : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) * Multiplicative.toAdd X)
  sec := ⊤
  ker := ⊥

section MultiNat

variable {W : Type} [CommGroup W]

@[expose] noncomputable def prodSubHom {m : ℕ} (I : Fin m → Subgroup W) : (∀ i, ↥(I i)) →* W where
  toFun x := ∏ i, (x i : W)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

theorem prodSubHom_apply {m : ℕ} (I : Fin m → Subgroup W) (x : ∀ i, ↥(I i)) :
    prodSubHom I x = ∏ i, (x i : W) := rfl

theorem prodSubHom_injective {m : ℕ} (I : Fin m → Subgroup W)
    (hind : ∀ i, I i ⊓ ⨆ (j : Fin m) (_ : j ≠ i), I j = ⊥) : Function.Injective (prodSubHom I) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  funext i
  have hx' : ∏ j, (x j : W) = 1 := hx
  have h1 : (x i : W) * ∏ j ∈ Finset.univ.erase i, (x j : W) = 1 := by
    rw [Finset.mul_prod_erase Finset.univ (fun j => (x j : W)) (Finset.mem_univ i)]
    exact hx'
  have hP : ∏ j ∈ Finset.univ.erase i, (x j : W) ∈ ⨆ (j : Fin m) (_ : j ≠ i), I j :=
    Subgroup.prod_mem _ fun j hj =>
      Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem (Finset.ne_of_mem_erase hj) (x j).2)
  have h2 : (x i : W) = (∏ j ∈ Finset.univ.erase i, (x j : W))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : (x i : W) ∈ I i ⊓ ⨆ (j : Fin m) (_ : j ≠ i), I j :=
    ⟨(x i).2, h2 ▸ (Subgroup.inv_mem _ hP)⟩
  rw [hind i, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

theorem prodSubHom_range {m : ℕ} (I : Fin m → Subgroup W) : (prodSubHom I).range = ⨆ i, I i := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [prodSubHom_apply]
    exact Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (x i).2
  · refine iSup_le fun i u hu => ⟨Pi.mulSingle i ⟨u, hu⟩, ?_⟩
    rw [prodSubHom_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem exists_coord_of_realizesVia {n : ℕ} {F : Type} [Field F] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (π : ↥(StatedSL n F) →* ↥L)
    (hreal : (FFModel.nat (StatedSL n F)).RealizesVia L U ⊥ π) :
    ∃ b : ↥U ≃* Multiplicative (Fin n → F),
      ∀ (γ : ↥(StatedSL n F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        b ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSL n F) γ (b u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hreal
  let q := topBotQuotEquiv (Multiplicative (Fin n → F))
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let b0 : ↥U →* Multiplicative (Fin n → F) := q.toMonoidHom.comp β
  refine ⟨MulEquiv.ofBijective b0 ⟨q.injective.comp hβinj, q.surjective.comp hβs⟩, ?_⟩
  intro γ u hu
  show b0 ⟨_, hu⟩ = natAct (StatedSL n F) γ (b0 u)
  have hum : β u = QuotientGroup.mk
      (⟨b0 u, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (Fin n → F)))) := by
    apply q.injective
    rfl
  exact congrArg q (hβe γ u ⟨b0 u, trivial⟩ hu trivial hum)

@[expose] def colsToMatrix (n m : ℕ) (F : Type) [Field F] :
    (Fin m → Multiplicative (Fin n → F)) ≃* Multiplicative (Matrix (Fin n) (Fin m) F) where
  toFun c := Multiplicative.ofAdd (Matrix.of fun j i => Multiplicative.toAdd (c i) j)
  invFun X := fun i => Multiplicative.ofAdd (fun j => Multiplicative.toAdd X j i)
  left_inv c := by
    funext i
    rfl
  right_inv X := by
    rfl
  map_mul' c d := by
    rfl

theorem colsToMatrix_natAct {n m : ℕ} {F : Type} [Field F] (γ : ↥(StatedSL n F))
    (c : Fin m → Multiplicative (Fin n → F)) :
    colsToMatrix n m F (fun i => natAct (StatedSL n F) γ (c i)) =
      Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Multiplicative.toAdd (colsToMatrix n m F c)) := by
  apply Multiplicative.toAdd.injective
  ext j i
  simp [colsToMatrix, natAct, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem realizesVia_multiNatModelU {n m : ℕ} {F : Type} [Field F] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (I : Fin m → Subgroup W) (π : ↥(StatedSL n F) →* ↥L)
    (hind : ∀ i, I i ⊓ ⨆ (j : Fin m) (_ : j ≠ i), I j = ⊥) (hU : ⨆ i, I i = U)
    (hπ : Function.Surjective π)
    (hreal : ∀ i, (FFModel.nat (StatedSL n F)).RealizesVia L (I i) ⊥ π) :
    (multiNatModelU n m F).RealizesVia L U ⊥ π := by
  choose b hb using fun i => exists_coord_of_realizesVia π (hreal i)
  have hinv : ∀ (g : ↥L) i, ∀ u ∈ I i, (g : MulAut W) u ∈ I i :=
    fun g i u hu => (hreal i).2.2.2.1 g u hu
  have hrange : (prodSubHom I).range = U := (prodSubHom_range I).trans hU
  have hmemU : ∀ x : (∀ i, ↥(I i)), prodSubHom I x ∈ U := fun x =>
    hrange ▸ (⟨x, rfl⟩ : prodSubHom I x ∈ (prodSubHom I).range)
  let Φ : (∀ i, ↥(I i)) ≃* ↥U := MulEquiv.ofBijective ((prodSubHom I).codRestrict U hmemU)
    ⟨fun x y hxy => prodSubHom_injective I hind (congrArg Subtype.val hxy), fun u => by
      obtain ⟨x, hx⟩ : (u : W) ∈ (prodSubHom I).range := hrange ▸ u.2
      exact ⟨x, Subtype.ext hx⟩⟩
  have hΦ : ∀ x, ((Φ x : ↥U) : W) = ∏ i, (x i : W) := fun x => rfl
  let Ψ : (∀ i, ↥(I i)) ≃* (Fin m → Multiplicative (Fin n → F)) := MulEquiv.piCongrRight b
  let βt : ↥U ≃* Multiplicative (Matrix (Fin n) (Fin m) F) :=
    Φ.symm.trans (Ψ.trans (colsToMatrix n m F))
  let q' := topBotQuotEquiv (Multiplicative (Matrix (Fin n) (Fin m) F))
  have hkey : ∀ (γ : ↥(StatedSL n F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
      βt ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          Multiplicative.toAdd (βt u)) := by
    intro γ u hu
    set x := Φ.symm u with hx
    have hux : u = Φ x := (Φ.apply_symm_apply u).symm
    let y : ∀ i, ↥(I i) := fun i => ⟨((π γ : ↥L) : MulAut W) (x i : W), hinv _ i _ (x i).2⟩
    have hu' : (u : W) = ∏ i, (x i : W) := (congrArg Subtype.val hux).trans (hΦ x)
    have hy : (⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ : ↥U) = Φ y := by
      apply Subtype.ext
      show ((π γ : ↥L) : MulAut W) (u : W) = ((Φ y : ↥U) : W)
      rw [hΦ, hu', map_prod]
    show colsToMatrix n m F (Ψ (Φ.symm ⟨_, hu⟩)) = _
    rw [hy, Φ.symm_apply_apply]
    have h1 : Ψ y = fun i => natAct (StatedSL n F) γ (Ψ x i) := by
      funext i
      exact hb i γ (x i) (hinv _ i _ (x i).2)
    show colsToMatrix n m F (Ψ y) = _
    rw [h1, colsToMatrix_natAct]
    show _ = Multiplicative.ofAdd (_ * Multiplicative.toAdd (colsToMatrix n m F (Ψ (Φ.symm u))))
    rfl
  refine ⟨hπ, bot_le, bot_le, ?_, fun g z hz => ?_, fun _ _ _ => trivial, fun γ z hz => ?_, ?_⟩
  · intro g u hu
    have hsub : (⨆ i, I i).map (g : MulAut W).toMonoidHom ≤ ⨆ i, I i := by
      rw [Subgroup.map_iSup]
      exact iSup_mono fun i => by
        rintro _ ⟨u, hu, rfl⟩
        exact hinv g i u hu
    exact hU ▸ hsub ⟨u, hU ▸ hu, rfl⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hz' : z = 1 := Subgroup.mem_bot.mp hz
    rw [hz']
    have h1 : ∀ γ' : ↥(StatedSL n F), (multiNatModelU n m F).act γ' 1 = 1 := by
      intro γ'
      show Multiplicative.ofAdd (((γ' : Matrix.GeneralLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *
          Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin n) (Fin m) F))) = 1
      rw [show Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin n) (Fin m) F)) = 0 from rfl,
        Matrix.mul_zero]
      rfl
    exact Subgroup.mem_bot.mpr (h1 γ)
  · refine ⟨q'.symm.toMonoidHom.comp βt.toMonoidHom, q'.symm.surjective.comp βt.surjective, ?_, ?_⟩
    · intro u
      rw [Subgroup.mem_bot]
      show q'.symm (βt u) = 1 ↔ (u : W) = 1
      rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    · intro γ u mm hu hm hum
      apply q'.injective
      have hum2 : q'.symm (βt u) = QuotientGroup.mk mm := hum
      have hum' : βt u = ((mm : (multiNatModelU n m F).Amb)) := by
        have h2 := congrArg q' hum2
        rw [MulEquiv.apply_symm_apply] at h2
        exact h2
      show q' (q'.symm (βt ⟨_, hu⟩)) = q' (QuotientGroup.mk ⟨_, hm⟩)
      refine (q'.apply_symm_apply _).trans ((hkey γ u hu).trans ?_)
      rw [hum']
      rfl

end MultiNat

section TildeSec

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem modelOnU_tilde_of_realizes_sec (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {X J : Subgroup G} (hXH : X ≤ H) (hJIH : J ≤ conjClosure I H)
    (hXJ : X ≤ Subgroup.normalizer (J : Set G)) {D : FFModel}
    (hD : D.Realizes (autIH V₁ I H X) (subM V₁ (conjClosure I H) J) ⊥) :
    ModelOnU D (tildeOf V₁ X) (tildeOf V₁ J) := by
  have hJU : J ≤ conjClosure Vp H := hJIH.trans (conjClosure_le_conjClosure_U hIU le_rfl)
  have hel : IsElemAbelian 2 (tildeOf V₁ J) := h.isElemAbelian_tilde_of_le hJU
  have hle : tildeOf V₁ J ≤ tildeOf V₁ (conjClosure I H) := secImg_mono hJIH
  have hYA : tildeOf V₁ X ≤
      Subgroup.normalizer ((tildeOf V₁ J : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg hXJ
  have hYB : tildeOf V₁ X ≤
      Subgroup.normalizer ((tildeOf V₁ (conjClosure I H) : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg (hXH.trans (le_normalizer_conjClosure I H))
  refine ⟨hYA, hel, ?_⟩
  obtain ⟨π, hπ⟩ := hD
  letI : CommGroup ↥(tildeOf V₁ J) := commGroupOfElemAbelian hel
  let V₀ : Subgroup ↥(tildeOf V₁ (conjClosure I H)) := subM V₁ (conjClosure I H) J
  let e : ↥V₀ ≃* ↥(tildeOf V₁ J) := Subgroup.subgroupOfEquivOfLe hle
  have hcoe : ∀ u : ↥V₀, ((e u : ↥(tildeOf V₁ J)) : GtOf V₁) =
      (((u : ↥(tildeOf V₁ (conjClosure I H))) : ↥(tildeOf V₁ (conjClosure I H))) : GtOf V₁) :=
    fun u => rfl
  have hstab : ∀ (n : GtOf V₁) (hnY : n ∈ tildeOf V₁ X),
      conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈ stabSub V₀ := by
    intro n hnY u
    show ((conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ u : ↥(tildeOf V₁ (conjClosure I H))) :
        GtOf V₁) ∈ tildeOf V₁ J ↔ (u : GtOf V₁) ∈ tildeOf V₁ J
    rw [AutOn.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hYA hnY) (u : GtOf V₁)).symm
  have hXst : autIH V₁ I H X ≤ stabSub V₀ := by
    intro g hg
    obtain ⟨⟨n, hn⟩, hnY, rfl⟩ := AutOn.mem_autOn_iff.mp hg
    exact hstab n hnY
  have key : ∀ (n : GtOf V₁) (hnY : n ∈ tildeOf V₁ X)
      (hg : conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈ stabSub V₀),
      MulAut.congr e (resHom V₀ ⟨conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩, hg⟩) =
        conjAct (tildeOf V₁ J) ⟨n, hYA hnY⟩ := by
    intro n hnY hg
    refine MulEquiv.ext fun a => Subtype.ext ?_
    show ((e (resHom V₀ ⟨_, hg⟩ (e.symm a)) : ↥(tildeOf V₁ J)) : GtOf V₁) =
      ((conjAct (tildeOf V₁ J) ⟨n, hYA hnY⟩ a : ↥(tildeOf V₁ J)) : GtOf V₁)
    rw [AutOn.coe_conjAct_apply, hcoe, resHom_apply]
    show (((conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩
      ((e.symm a : ↥V₀) : ↥(tildeOf V₁ (conjClosure I H))) : ↥(tildeOf V₁ (conjClosure I H))) :
        GtOf V₁)) = _
    rw [AutOn.coe_conjAct_apply]
    have h1 := hcoe (e.symm a)
    rw [e.apply_symm_apply] at h1
    rw [← h1]
  let τ0 : ↥(autIH V₁ I H X) →* MulAut ↥(tildeOf V₁ J) :=
    (MulAut.congr e).toMonoidHom.comp (resHomOn V₀ hXst)
  have hτmem : ∀ x : ↥(autIH V₁ I H X), τ0 x ∈ autOn (tildeOf V₁ X) (tildeOf V₁ J) := by
    rintro ⟨g, hg⟩
    obtain ⟨⟨n, hn⟩, hnY, rfl⟩ := AutOn.mem_autOn_iff.mp hg
    exact AutOn.mem_autOn_iff.mpr ⟨⟨n, hYA hnY⟩, hnY, (key n hnY (hstab n hnY)).symm⟩
  let τ : ↥(autIH V₁ I H X) →* ↥(autOn (tildeOf V₁ X) (tildeOf V₁ J)) := τ0.codRestrict _ hτmem
  have hτs : Function.Surjective τ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨⟨n, hnA⟩, hnY, rfl⟩ := AutOn.mem_autOn_iff.mp hψ
    have hmem : conjAct (tildeOf V₁ (conjClosure I H)) ⟨n, hYB hnY⟩ ∈ autIH V₁ I H X :=
      AutOn.mem_autOn_iff.mpr ⟨⟨n, hYB hnY⟩, hnY, rfl⟩
    exact ⟨⟨_, hmem⟩, Subtype.ext (key n hnY (hstab n hnY))⟩
  let ρ : ↥V₀ →* ↥(tildeOf V₁ J) := e.toMonoidHom
  have hρk : ∀ u : ↥V₀, ρ u = 1 ↔ (u : ↥(tildeOf V₁ (conjClosure I H))) ∈
      (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure I H))) := by
    intro u
    rw [Subgroup.mem_bot]
    show e u = 1 ↔ (u : ↥(tildeOf V₁ (conjClosure I H))) = 1
    rw [map_eq_one_iff e e.injective]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  refine ⟨τ.comp π, realizesVia_transport (H' := autOn (tildeOf V₁ X) (tildeOf V₁ J))
    hπ ρ e.surjective hρk τ hτs ?_⟩
  intro x u hu
  show e ((resHomOn V₀ hXst x) (e.symm (e (u : ↥V₀)))) = e ⟨(x : MulAut _) (u : _), hu⟩
  rw [e.symm_apply_apply]
  rfl

end TildeSec

section CaseC

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem five_iii_c_model (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hC : D321Two (autIH V₁ I H K)) :
    LieModel ↥(autIH V₁ Vp H K) .PSL 3 2 1 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        ModelOnU (multiNatModelU 3 4 F) (tildeOf V₁ K) (tildeOf V₁ ⁅conjClosure I H, K⁆) := by
  obtain ⟨hPSL, I', π, -, hind, hsup, hreal⟩ := hC
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hIH := le_normalizer_conjClosure I H
  obtain ⟨eA⟩ := autIH_equiv h hH hA37 hA38 hK hIU hnt
  refine ⟨lieModel_of_isPSL (isPSL_congr eA.symm hPSL), ZMod 2, inferInstance, inferInstance,
    Nat.card_zmod 2, ?_⟩
  have hind' : ∀ i, I' i ⊓ ⨆ (j : Fin 4) (_ : j ≠ i), I' j = ⊥ := fun i => by
    simpa only [bot_sup_eq] using hind i
  have hU : ⨆ i, I' i = commV (autIH V₁ I H K) := by
    simpa only [bot_sup_eq] using hsup
  have hreal' := realizesVia_multiNatModelU (n := 3) (m := 4) (F := ZMod 2) I' π hind' hU
    (hreal 0).1 hreal
  rw [commV_autIH_eq_subM h hIU hKH] at hreal'
  have hJIH : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKH.trans hIH)
  exact modelOnU_tilde_of_realizes_sec h hIU hKH hJIH
    (F9.le_normalizer_commutator_of_le (hKH.trans hIH) (Subgroup.le_normalizer))
    ⟨π, hreal'⟩

end CaseC

end CFSG.Quasithin.RonanF918
