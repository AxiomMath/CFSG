module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzc
public import CFSG.Quasithin.Background.F918C12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix IsMulCommutative

@[expose] noncomputable def secQ : ↥(⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 2))) ⧸
    ((⊥ : Subgroup (Multiplicative (Fin 5 → ZMod 2))).subgroupOf ⊤) →*
      Multiplicative (Fin 5 → ZMod 2) :=
  QuotientGroup.lift _ (⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 2))).subtype fun _ hx =>
    MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hx))

theorem secQ_mk (m : ↥(⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 2)))) :
    secQ (QuotientGroup.mk m) = (m : Multiplicative (Fin 5 → ZMod 2)) := rfl

theorem secQ_injective : Function.Injective secQ := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [secQ_mk] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    exact hq

theorem exists_coordOfReal {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {Γ : Type} [Group Γ] {π : Γ →* ↥H}
    {act : Γ → Multiplicative (Fin 5 → ZMod 2) → Multiplicative (Fin 5 → ZMod 2)}
    (h : (FFModel.mk Γ (Multiplicative (Fin 5 → ZMod 2)) act ⊤ ⊥).RealizesVia H U ⊥ π) :
    ∃ e : ↥U ≃* Multiplicative (Fin 5 → ZMod 2), ∀ (γ : Γ) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U), e ⟨_, hu⟩ = act γ (e u) := by
  obtain ⟨-, -, -, -, -, -, -, β₀, hβs, hβk, hβe⟩ := h
  let β : ↥U →* ↥(⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 2))) ⧸
      ((⊥ : Subgroup (Multiplicative (Fin 5 → ZMod 2))).subgroupOf ⊤) := β₀
  have hβs' : Function.Surjective β := hβs
  have hβk' : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := hβk
  have hβe' : ∀ (γ : Γ) (u : ↥U) (m : ↥(⊤ : Subgroup (Multiplicative (Fin 5 → ZMod 2))))
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U), β u = QuotientGroup.mk m →
        β ⟨_, hu⟩ = QuotientGroup.mk ⟨act γ (m : Multiplicative (Fin 5 → ZMod 2)), trivial⟩ :=
    fun γ u m hu hm => hβe γ u m hu trivial hm
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk' u).1 hu
    exact Subtype.ext (by simpa using this)
  have hfi : Function.Injective (secQ.comp β) := secQ_injective.comp hβi
  have hfs : Function.Surjective (secQ.comp β) := by
    intro y
    obtain ⟨u, hu⟩ := hβs' (QuotientGroup.mk ⟨y, trivial⟩)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu, secQ_mk]⟩
  refine ⟨MulEquiv.ofBijective (secQ.comp β) ⟨hfi, hfs⟩, fun γ u hu => ?_⟩
  have hβu : β u = QuotientGroup.mk ⟨secQ (β u), trivial⟩ :=
    secQ_injective (by rw [secQ_mk])
  have h1 := hβe' γ u ⟨secQ (β u), trivial⟩ hu hβu
  show secQ (β ⟨_, hu⟩) = act γ (secQ (β u))
  rw [h1, secQ_mk]

variable {G : Type} [Group G]

theorem exists_multiCoord {J W : Subgroup G} [IsMulCommutative ↥W]
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) {k : ℕ}
    (π : ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) →* ↥(autOn J W)) (hπ : Function.Bijective π)
    (U : Fin k → Subgroup ↥W) (hind : iSupIndep U) (hsup : ⨆ i, U i = ⊤) (dual : Fin k → Bool)
    (hnat : ∀ i, dual i = false →
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))).RealizesVia (autOn J W) (U i) ⊥ π)
    (hdual : ∀ i, dual i = true →
      (FFModel.dualNat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))).RealizesVia (autOn J W) (U i) ⊥
        π) :
    ∃ C : MultiCoord J W k, C.dual = dual := by
  classical
  let eSL := Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)
  have heSL : ∀ γ : ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
      (((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) =
        ((eSL.symm γ : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := fun γ => by
    have := Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) (eSL.symm γ)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  let πe := MulEquiv.ofBijective π hπ
  let σ : ↥J →* ↥(autOn J W) := (Setup.rho W J hJW).codRestrict (autOn J W)
    fun j => (Setup.mem_autOn_self_iff hJW).2 ⟨j, rfl⟩
  have hσ : Function.Surjective σ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨j, rfl⟩ := (Setup.mem_autOn_self_iff hJW).1 hφ
    exact ⟨j, rfl⟩
  let ρ : ↥J →* SL5 := (eSL.symm.toMonoidHom.comp πe.symm.toMonoidHom).comp σ
  have hρ : ∀ j : ↥J, π (eSL (ρ j)) = σ j := fun j => by
    show π (eSL (eSL.symm (πe.symm (σ j)))) = σ j
    rw [MulEquiv.apply_symm_apply]
    exact πe.apply_symm_apply (σ j)
  have hinv : ∀ i (φ : ↥(autOn J W)) (u : ↥W), u ∈ U i → (φ : MulAut ↥W) u ∈ U i := by
    intro i φ u hu
    cases hd : dual i
    · exact (hnat i hd).2.2.2.1 φ u hu
    · exact (hdual i hd).2.2.2.1 φ u hu
  have hcoord : ∀ i, ∃ e : ↥(U i) ≃* Multiplicative (Fin 5 → ZMod 2),
      ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) (u : ↥(U i))
      (hu : ((π γ : ↥(autOn J W)) : MulAut ↥W) (u : ↥W) ∈ U i),
      Multiplicative.toAdd (e ⟨_, hu⟩) =
        (tw (dual i) (eSL.symm γ) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (e u) := by
    intro i
    cases hd : dual i
    · obtain ⟨e, he⟩ := exists_coordOfReal (hnat i hd)
      refine ⟨e, fun γ u hu => ?_⟩
      rw [he γ u hu, tw_false]
      show Multiplicative.toAdd (Multiplicative.ofAdd
        ((((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) *ᵥ
          Multiplicative.toAdd (e u))) = _
      rw [toAdd_ofAdd, heSL]
    · obtain ⟨e, he⟩ := exists_coordOfReal (hdual i hd)
      refine ⟨e, fun γ u hu => ?_⟩
      rw [he γ u hu, tw_true]
      show Multiplicative.toAdd (Multiplicative.ofAdd
        ((((γ⁻¹ : ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) : GL (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd (e u))) = _
      rw [toAdd_ofAdd, heSL, map_inv]
  choose e he using hcoord
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : ↥W, x ∈ U i → y ∈ U j → Commute x y :=
    fun _ _ _ x y _ _ => Commute.all x y
  have hΦi : Function.Injective (Subgroup.noncommPiCoprod hcomm) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hΦs : Function.Surjective (Subgroup.noncommPiCoprod hcomm) := by
    intro v
    have hv : v ∈ (Subgroup.noncommPiCoprod hcomm).range := by
      rw [Subgroup.noncommPiCoprod_range, hsup]
      trivial
    obtain ⟨x, hx⟩ := hv
    exact ⟨x, hx⟩
  let Φe := MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm) ⟨hΦi, hΦs⟩
  have hΦ : ∀ x, Φe x = ∏ i, (x i : ↥W) := fun x => by
    show Subgroup.noncommPiCoprod hcomm x = _
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  have hdec : ∀ (φ : ↥(autOn J W)) (v : ↥W) (i : Fin k),
      Φe.symm ((φ : MulAut ↥W) v) i =
        ⟨(φ : MulAut ↥W) (Φe.symm v i), hinv i φ _ (Φe.symm v i).2⟩ := by
    intro φ v
    have hy : Φe.symm ((φ : MulAut ↥W) v) =
        fun i => ⟨(φ : MulAut ↥W) (Φe.symm v i), hinv i φ _ (Φe.symm v i).2⟩ := by
      apply Φe.injective
      rw [MulEquiv.apply_symm_apply, hΦ]
      conv_lhs => rw [← Φe.apply_symm_apply v, hΦ, map_prod]
    intro i
    rw [hy]
  let E : G → Fin k → Fin 5 → ZMod 2 := fun g =>
    if hg : g ∈ W then fun i => Multiplicative.toAdd (e i (Φe.symm ⟨g, hg⟩ i)) else 0
  have hEW : ∀ g (hg : g ∈ W) i, E g i = Multiplicative.toAdd (e i (Φe.symm ⟨g, hg⟩ i)) :=
    fun g hg i => by simp only [E, dite_eq_left hg]
  refine ⟨⟨E, ρ, dual, hJW, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro a ha b hb
    funext i
    rw [Pi.add_apply, hEW _ (W.mul_mem ha hb), hEW _ ha, hEW _ hb]
    have hab : (⟨a * b, W.mul_mem ha hb⟩ : ↥W) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [hab, _root_.map_mul, Pi.mul_apply, _root_.map_mul, toAdd_mul]
  · intro a ha b hb hab
    have h1 : Φe.symm ⟨a, ha⟩ = Φe.symm ⟨b, hb⟩ := funext fun i => (e i).injective
      (Multiplicative.toAdd.injective (by rw [← hEW a ha i, ← hEW b hb i, hab]))
    exact congrArg Subtype.val (Φe.symm.injective h1)
  · intro x
    let u : ∀ i, ↥(U i) := fun i => (e i).symm (Multiplicative.ofAdd (x i))
    refine ⟨(Φe u : ↥W), (Φe u).2, ?_⟩
    funext i
    rw [hEW _ (Φe u).2, Subtype.coe_eta, MulEquiv.symm_apply_apply]
    simp [u]
  · intro j a ha i
    have hja : (j : G) * a * (j : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hJW j.2) a).mp ha
    rw [hEW _ hja, hEW _ ha]
    have h1 : (⟨(j : G) * a * (j : G)⁻¹, hja⟩ : ↥W) =
        ((π (eSL (ρ j)) : ↥(autOn J W)) : MulAut ↥W) ⟨a, ha⟩ := by
      rw [hρ j]
      exact Subtype.ext (Setup.rho_apply_coe hJW j ⟨a, ha⟩).symm
    rw [h1, hdec, he i (eSL (ρ j)), MulEquiv.symm_apply_apply]
  · exact (eSL.symm.surjective.comp πe.symm.surjective).comp hσ

theorem exists_multiCoord_of_sumNatDual {J W : Subgroup G} [IsMulCommutative ↥W]
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) (h : SumNatDual (autOn J W) ⊤ 5) :
    ∃ C : MultiCoord J W 2, C.dual = ![false, true] := by
  obtain ⟨-, π, U₁, U₂, ⟨hsup, hinf⟩, h₁, h₂⟩ := h
  have hπ : Function.Bijective π :=
    ⟨realizesVia_injective_of_faithful (FFModel.nat_faithful _) h₁, h₁.1⟩
  refine exists_multiCoord hJW π hπ ![U₁, U₂] ?_ ?_ ![false, true] ?_ ?_
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    exact disjoint_iff.mpr hinf
  · refine le_antisymm le_top ?_
    rw [← hsup]
    exact sup_le (le_iSup (![U₁, U₂]) 0) (le_iSup (![U₁, U₂]) 1)
  · intro i hi
    fin_cases i
    · exact h₁
    · exact absurd hi (by decide)
  · intro i hi
    fin_cases i
    · exact absurd hi (by decide)
    · exact h₂

theorem exists_multiCoord_of_copies {J W : Subgroup G} [IsMulCommutative ↥W]
    (hJW : J ≤ Subgroup.normalizer (W : Set G)) {k : ℕ} (hk : 1 ≤ k)
    (h : DirectSumOfCopies (autOn J W) ⊤ ⊥
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) k) :
    ∃ C : MultiCoord J W k, C.dual = fun _ => false := by
  obtain ⟨U, π, -, hind, hsup, hreal⟩ := h
  have hπ : Function.Bijective π :=
    ⟨realizesVia_injective_of_faithful (FFModel.nat_faithful _) (hreal ⟨0, hk⟩),
      (hreal ⟨0, hk⟩).1⟩
  refine exists_multiCoord hJW π hπ U ?_ ?_ (fun _ => false) (fun i _ => hreal i)
    (fun _ hi => absurd hi (by simp))
  · rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    have := hind i
    rwa [bot_sup_eq] at this
  · rw [← hsup, bot_sup_eq]

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
