module

public import CFSG.RankThree.S4Free.Stellmacher33Step
public import CFSG.RankThree.S4Free.Stellmacher33Fusion
public import CFSG.RankThree.S4Free.Stellmacher33Bridge

public section

namespace CFSG.RankThree.S4Free.Stell33

open Subgroup CFSG.Quasithin CFSG.Open

universe u v

section Normalizers

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj {K : Subgroup G} {g : G} (h₁ : ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, g⁻¹ * x * g ∈ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  have := h₂ _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (A : Set G) → g' ∈ normalizer (B : Set G) →
      A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g').toMonoidHom := fun g' hA' hB' =>
    sup_le (fun x hx => mem_sup_left ((mem_normalizer_iff.mp hA' x).mp hx))
      (fun x hx => mem_sup_right ((mem_normalizer_iff.mp hB' x).mp hx))
  refine mem_normalizer_of_conj (fun x hx => key g hA hB hx) (fun x hx => ?_)
  have := key g⁻¹ (inv_mem hA) (inv_mem hB) hx
  change g⁻¹ * x * g⁻¹⁻¹ ∈ A ⊔ B at this
  rwa [inv_inv] at this

end Normalizers

theorem false_of_isL24 {𝒦 : HostClass} {S : Type u} [Group S] [Finite S] (hThmA : ThmA.{u} 𝒦)
    {H : Type v} [Group H] {κ : S →* H} (hκ : F2Host 𝒦 κ) {M L : Subgroup H}
    (hMW : M ≤ normalizer (((stellW 𝒦 S).map κ : Subgroup H) : Set H))
    (hL : Stell.IsL24 κ.range M ((stellW 𝒦 S).map κ) L) : False := by
  haveI := hκ.admissible.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := hκ.admissible.injective
  have hS3 : IsSym3Free H := hκ.admissible.isSym3Free
  obtain ⟨Tsyl, hTsyl⟩ := hκ.admissible.sylow
  haveI : (stellW 𝒦 S).Characteristic := stellW_characteristic
  have hT2 : IsPGroup 2 κ.range := hTsyl ▸ Tsyl.isPGroup'
  have hS2 : IsPGroup 2 S :=
    hT2.of_injective κ.rangeRestrict (fun a b hab => hinj (congrArg Subtype.val hab))
  have hWhT : (stellW 𝒦 S).map κ ≤ κ.range := map_le_range κ _
  have hTW := range_le_normalizer_map κ (inferInstance : (stellW 𝒦 S).Normal)
  have hWel : IsElemAbelian 2 ((stellW 𝒦 S).map κ) :=
    Stell.isElemAbelian_map isElemAbelian_stellW κ
  have hOT : oTwo H ≤ κ.range := hTsyl ▸ (Stell.oTwo_isPGroup H).le_sylow_of_normal Tsyl
  set W := stellW 𝒦 S with hW
  set Wh := W.map κ with hWh
  obtain ⟨u, hcfg, h3, hnp⟩ := exists_lcfg hS3 hT2 hMW hTW hWel hL
  set P := oTwoSub L with hP
  have hPX : P ≤ LCfg.X Wh P u := hcfg.P_le_X hnp
  have hXP : LCfg.X Wh P u ≤ P := hcfg.X_le_P
  have hXT : LCfg.X Wh P u ≤ κ.range :=
    hXP.trans (oTwoSub_le_of_relIndex hT2 hL.not_dvd_relIndex)
  set X := LCfg.X Wh P u with hX
  set XS := X.comap κ with hXS
  have hXSmap : XS.map κ = X := map_comap_eq_self hXT
  set Pd := XS ⊔ W with hPd
  have hPdmap : Pd.map κ = X ⊔ Wh := by rw [hPd, Subgroup.map_sup, hXSmap]
  let e : ↥Pd ≃* ↥(X ⊔ Wh) :=
    (Subgroup.equivMapOfInjective Pd κ hinj).trans (MulEquiv.subgroupCongr hPdmap)
  have he : ∀ p : ↥Pd, ((e p : ↥(X ⊔ Wh)) : H) = κ p := fun _ => rfl
  have hbase : ∀ φ : ↥Pd →* S, IsF1Fusion 𝒦 Pd φ →
      omegaOneCenterOf (⊤ : Subgroup S) ≤ (XS.subgroupOf Pd).map φ := by
    intro φ hφ z hz
    by_contra hzX
    have hzW : z ∈ W := omegaOneCenterOf_le_stellW hz
    obtain ⟨p, hp⟩ := hφ.exists_eq_of_mem_stellW le_sup_right hzW
    have hpW : (p : S) ∈ W := (hφ.mem_stellW_iff p).mp (hp ▸ hzW)
    have hpX : (p : S) ∉ XS := fun h => hzX ⟨p, h, hp⟩
    have hzc : ∀ s : S, s * z = z * s := fun s =>
      mem_centralizer_iff.mp (omegaOneCenterOf_le_centerOf _ hz).2 s (mem_top s)
    have hpc : ∀ x ∈ XS, (p : S) * x = x * p := by
      intro x hx
      have hxPd : x ∈ Pd := mem_sup_left hx
      have h1 : φ (p * ⟨x, hxPd⟩) = φ (⟨x, hxPd⟩ * p) := by
        rw [map_mul, map_mul, hp, (hzc _).symm]
      exact congrArg Subtype.val (hφ.injective h1)
    refine hcfg.false_of_centralizes hnp (Q := oTwo H) (Stell.oTwo_isPGroup H)
      hκ.admissible.centralizer_le ?_ (v := κ p) ⟨p, hpW, rfl⟩ ?_ ?_
    · intro q hq g hg
      have hqT : q ∈ κ.range := hOT hq
      have hqW : q ∈ normalizer (Wh : Set H) := hTW hqT
      have hqWu : q ∈ normalizer ((LCfg.Wu Wh u : Subgroup H) : Set H) := by
        have hq' : u⁻¹ * q * u ∈ normalizer (Wh : Set H) := by
          apply hTW
          apply hOT
          have := (inferInstance : (oTwo H).Normal).conj_mem q hq u⁻¹
          rwa [inv_inv] at this
        rw [mem_normalizer_iff]
        intro x
        rw [LCfg.Wu, mem_map_conj_iff, mem_map_conj_iff]
        have e1 : u⁻¹ * (q * x * q⁻¹) * u =
            (u⁻¹ * q * u) * (u⁻¹ * x * u) * (u⁻¹ * q * u)⁻¹ := by group
        rw [e1]
        exact mem_normalizer_iff.mp hq' _
      have hqL : q ∈ normalizer (L : Set H) := by
        rw [← hcfg.sup_eq]
        exact mem_normalizer_sup_of_mem hqW hqWu
      have h1 : q * g * q⁻¹ * g⁻¹ ∈ L :=
        mul_mem ((mem_normalizer_iff.mp hqL g).mp hg) (inv_mem hg)
      have h2 : q * g * q⁻¹ * g⁻¹ ∈ oTwo H := by
        have := (inferInstance : (oTwo H).Normal).conj_mem _ (inv_mem hq) g
        rw [show q * g * q⁻¹ * g⁻¹ = q * (g * q⁻¹ * g⁻¹) by group]
        exact mul_mem hq this
      refine le_oTwoSub (N := L ⊓ oTwo H) inf_le_left ?_
        ((Stell.oTwo_isPGroup H).to_le inf_le_right) (mem_inf.mpr ⟨h1, h2⟩)
      exact le_normalizer_of_forall_conj_mem (fun g' hg' x hx =>
        mem_inf.mpr ⟨mul_mem (mul_mem hg' (mem_inf.mp hx).1) (inv_mem hg'),
          (inferInstance : (oTwo H).Normal).conj_mem _ (mem_inf.mp hx).2 g'⟩)
    · intro hA
      exact hpX (hPX hA.2)
    · intro x hx
      have hx' : x ∈ XS.map κ := by rw [hXSmap]; exact hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx'
      rw [← map_mul, ← map_mul, hpc x₀ hx₀]
  have hstep : ∀ U : Subgroup S, (U.Normal ∧ ∀ φ : ↥Pd →* S, IsF1Fusion 𝒦 Pd φ →
        U ≤ (XS.subgroupOf Pd).map φ) →
      omegaOneCenterOf (⊤ : Subgroup S) ≤ U → U ≤ stellW 𝒦 S →
      ∀ (K : Type u) [Group K] (ι : S →* K), F1Host 𝒦 ι → ¬ (U.map ι).Normal →
      ((normalClosure ((U.map ι : Subgroup K) : Set K)).comap ι).Normal ∧
        ∀ φ : ↥Pd →* S, IsF1Fusion 𝒦 Pd φ →
          (normalClosure ((U.map ι : Subgroup K) : Set K)).comap ι ≤
            (XS.subgroupOf Pd).map φ := by
    rintro U ⟨hUn, hU⟩ - hUW K _ ι hι hnn
    refine ⟨normalClosure_normal.comap ι, fun φ hφ => ?_⟩
    by_contra hU'X
    haveI := hι.admissible.finite
    haveI : (pResidual 2 K).Normal := normal_pResidual 2 K
    have hιW : (W.map ι).Normal := stellW_normal hι
    have hιWO : W.map ι ≤ oTwo K := Stell.le_oTwo ((hS2.to_subgroup W).map ι)
    let θ : ↥(X ⊔ Wh) →* K := ι.comp (φ.comp e.symm.toMonoidHom)
    have hθe : ∀ p : ↥Pd, θ (e p) = ι (φ p) := fun p => by simp [θ]
    have hθ : Function.Injective θ :=
      hι.admissible.injective.comp (hφ.injective.comp e.symm.injective)
    have hθT : ∀ y, θ y ∈ ι.range := fun y => ⟨_, rfl⟩
    have himgW : img θ Wh = W.map ι := by
      ext k
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨p, rfl⟩ := e.surjective y
        have hpW : (p : S) ∈ W := by
          have h1 := mem_subgroupOf.mp hy
          rw [he] at h1
          exact (mem_map_iff_mem hinj).mp h1
        rw [hθe]
        exact ⟨φ p, (hφ.mem_stellW_iff p).mpr hpW, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨p, hp⟩ := hφ.exists_eq_of_mem_stellW le_sup_right hw
        have hpW : (p : S) ∈ W := (hφ.mem_stellW_iff p).mp (hp ▸ hw)
        refine ⟨e p, ?_, by rw [hθe, hp]⟩
        change ((e p : ↥(X ⊔ Wh)) : H) ∈ Wh
        rw [he]
        exact ⟨p, hpW, rfl⟩
    have hθW : img θ Wh ≤ oTwo K := himgW ▸ hιWO
    set V₀ := normalClosure ((U.map ι : Subgroup K) : Set K) with hV₀
    have hV₀W : V₀ ≤ img θ Wh := by
      rw [himgW]
      exact normalClosure_le_normal (map_mono hUW)
    have hV : ⁅V₀, pResidual 2 K⁆ ≠ ⊥ := by
      intro hbot
      apply hnn
      rw [normal_map_iff_pResidual_le_normalizer hι.admissible.sylow hUn]
      have hc : pResidual 2 K ≤ centralizer (V₀ : Set K) := by
        rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
        exact hbot
      intro r hr
      exact centralizer_le_normalizer _ (centralizer_le subset_normalClosure (hc hr))
    have hUA : U.map ι ≤ img θ (LCfg.A Wh P) := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨p, hp, hpt⟩ := hU φ hφ ht
      have hpW : (p : S) ∈ W := (hφ.mem_stellW_iff p).mp (hpt ▸ hUW ht)
      refine ⟨e p, ?_, by rw [hθe, hpt]⟩
      change ((e p : ↥(X ⊔ Wh)) : H) ∈ LCfg.A Wh P
      rw [he]
      exact mem_inf.mpr ⟨⟨p, hpW, rfl⟩, hXP (mem_subgroupOf.mp hp)⟩
    have hV₀A : V₀ ≤ ⁅V₀, pResidual 2 K⁆ ⊔ img θ (LCfg.A Wh P) := by
      have hR : ∀ r ∈ pResidual 2 K, U.map ι ⊔ ⁅V₀, pResidual 2 K⁆ ≤
          (U.map ι ⊔ ⁅V₀, pResidual 2 K⁆).comap (MulAut.conj r).toMonoidHom := by
        intro r hr
        refine sup_le (fun t ht => ?_) (fun x hx =>
          mem_sup_right ((inferInstance : (⁅V₀, pResidual 2 K⁆).Normal).conj_mem x hx r))
        change r * t * r⁻¹ ∈ U.map ι ⊔ ⁅V₀, pResidual 2 K⁆
        have hc : r * t * r⁻¹ * t⁻¹ ∈ ⁅V₀, pResidual 2 K⁆ := by
          rw [commutator_comm]
          exact commutator_mem_commutator hr (subset_normalClosure ht)
        rw [show r * t * r⁻¹ = (r * t * r⁻¹ * t⁻¹) * t by group]
        exact mul_mem (mem_sup_right hc) (mem_sup_left ht)
      haveI hnorm : (U.map ι ⊔ ⁅V₀, pResidual 2 K⁆).Normal := by
        rw [← normalizer_eq_top_iff, eq_top_iff, ← range_sup_pResidual_eq_top hι.admissible.sylow]
        refine sup_le (fun g hg => mem_normalizer_sup_of_mem (range_le_normalizer_map ι hUn hg)
          ?_) (fun r hr => mem_normalizer_of_conj (fun x hx => hR r hr hx) (fun x hx => ?_))
        · rw [normalizer_eq_top_iff.mpr inferInstance]
          exact mem_top g
        · have := hR r⁻¹ (inv_mem hr) hx
          change r⁻¹ * x * r⁻¹⁻¹ ∈ U.map ι ⊔ ⁅V₀, pResidual 2 K⁆ at this
          rwa [inv_inv] at this
      calc V₀ ≤ U.map ι ⊔ ⁅V₀, pResidual 2 K⁆ :=
            normalClosure_le_normal (fun x hx => mem_sup_left hx)
        _ ≤ ⁅V₀, pResidual 2 K⁆ ⊔ img θ (LCfg.A Wh P) :=
          sup_le (hUA.trans le_sup_right) le_sup_left
    have hV₀X : ¬ V₀ ≤ img θ X := by
      intro hle
      apply hU'X
      intro s hs
      obtain ⟨y, hy, hys⟩ := hle hs
      obtain ⟨p, rfl⟩ := e.surjective y
      rw [hθe] at hys
      refine ⟨p, ?_, hι.admissible.injective hys⟩
      have h1 := mem_subgroupOf.mp hy
      rw [he] at h1
      exact h1
    have hstep' : ∀ k : K, (∀ y, k * θ y * k⁻¹ ∈ ι.range) →
        ∀ t ∈ U.map ι, k⁻¹ * t * k ∈ img θ X := by
      intro k hk t ht
      have hk' : ∀ p : ↥Pd, k * ι (φ p) * k⁻¹ ∈ ι.range := fun p => by
        have := hk (e p)
        rwa [hθe] at this
      obtain ⟨ψ, hψ, hψe⟩ := hφ.exists_step hι k hk'
      obtain ⟨s, hs, rfl⟩ := ht
      obtain ⟨p, hp, hps⟩ := hU ψ hψ hs
      refine ⟨e p, ?_, ?_⟩
      · change ((e p : ↥(X ⊔ Wh)) : H) ∈ X
        rw [he]
        exact mem_subgroupOf.mp hp
      · rw [hθe, ← hps, hψe]
        group
    exact hcfg.false_of_step_of_thmA h3 hThmA hι.holds hι.admissible.isSym3Free
      hι.admissible.sylow hι.condM θ hθ hθT hθW hV₀W hV hV₀A hV₀X le_rfl hstep'
  have hall := stellW_induction (𝒦 := 𝒦) (S := S)
    (fun U => U.Normal ∧ ∀ φ : ↥Pd →* S, IsF1Fusion 𝒦 Pd φ →
      U ≤ (XS.subgroupOf Pd).map φ)
    ⟨normal_omegaOneCenterOf' ⊤, hbase⟩ hstep
  have hWX : W ≤ XS := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := hall.2 Pd.subtype .refl hw
    exact mem_subgroupOf.mp hp
  have hWP : Wh ≤ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact hXP (hWX hw)
  have h1 : (Wh ⊓ P).relIndex Wh = 1 := relIndex_eq_one.mpr (le_inf le_rfl hWP)
  have h2 := hcfg.relIndex_eq
  omega

theorem isCoatom_normalizer_of_minimal {𝒦 : HostClass} {S : Type u} [Group S] [Finite S]
    {H : Type v} [Group H] {κ : S →* H} (hκ : F2Host 𝒦 κ)
    (hnot : ¬ ((stellW 𝒦 S).map κ).Normal)
    (hmin : ∀ K : Subgroup H, κ.range ≤ K → K ≠ ⊤ →
      K ≤ normalizer (((stellW 𝒦 S).map κ : Subgroup H) : Set H))
    (h32 : ¬ (stellW 𝒦 S).map κ ≤ oTwo H) :
    IsCoatom (normalizer (((stellW 𝒦 S).map κ : Subgroup H) : Set H)) ∧
      ¬ (stellW 𝒦 S).map κ ≤
        (normalizer (((stellW 𝒦 S).map κ : Subgroup H) : Set H)).normalCore := by
  haveI := hκ.admissible.finite
  haveI : (stellW 𝒦 S).Characteristic := stellW_characteristic
  have hTW := range_le_normalizer_map κ (inferInstance : (stellW 𝒦 S).Normal)
  set Wh := (stellW 𝒦 S).map κ with hWh
  have hMtop : normalizer (Wh : Set H) ≠ ⊤ := fun h => hnot (normalizer_eq_top_iff.mp h)
  refine ⟨⟨hMtop, fun K hK => ?_⟩, fun hle => ?_⟩
  · by_contra hKt
    exact (not_le_of_gt hK) (hmin K (hTW.trans hK.le) hKt)
  · rcases hκ.condM (normalizer (Wh : Set H)).normalCore inferInstance with h1 | h1
    · exact h32 (fun x hx => h1 ⟨map_le_range κ _ hx, hle hx⟩)
    · apply hMtop
      rw [eq_top_iff, ← range_sup_pResidual_eq_top hκ.admissible.sylow]
      exact sup_le hTW (h1.trans (normalCore_le _))

end CFSG.RankThree.S4Free.Stell33
