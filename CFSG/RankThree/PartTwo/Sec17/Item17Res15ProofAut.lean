module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.LieType.SteinbergBRSmallAltSylow
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec16.Steps166 CFSG.ComponentClassification.OuterAutomorphisms

section NoSz

theorem noSzSection_mulAut_of_outer {S : Type} [Group S]
    [Finite S] (hS : NoSzSection S) (h5 : ¬ 5 ∣ Nat.card (Outer S)) :
    NoSzSection (MulAut S) := by
  intro X N _ p f hSz
  have : Finite (MulAut S) := KFacts.KP7.finite_mulAut S
  have hsimp : IsSimpleGroup (↥X ⧸ N) := Sec16.isSimpleGroup_of_suzukiModel hSz
  set XI : Subgroup ↥X := (inner S).comap X.subtype with hXI
  have hXIn : XI.Normal := Subgroup.Normal.comap (inner_normal S) X.subtype
  have hmapn : (XI.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map hXIn _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (XI.map (QuotientGroup.mk' N)) with h | h
  ·
    have hXIN : XI ≤ N := by
      intro x hx
      have h1 : QuotientGroup.mk' N x ∈ XI.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hx
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    set ψ : ↥X →* Outer S := (QuotientGroup.mk' (inner S)).comp X.subtype with hψ
    have hker : ψ.ker = XI := by
      ext x
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hXI, Subgroup.mem_comap]
    have h1 : Nat.card (↥X ⧸ N) ∣ Nat.card (↥X ⧸ XI) := Subgroup.index_dvd_of_le hXIN
    have h2 : Nat.card (↥X ⧸ XI) ∣ Nat.card (Outer S) := by
      rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact h5 ((Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hSz).trans (h1.trans h2))
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp XI.subtype) := by
      intro q
      have hq : q ∈ XI.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    have hI : NoSzSection ↥(inner S) :=
      Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
        (MulAut.conj : S →* MulAut S).rangeRestrict
        (MulAut.conj : S →* MulAut S).rangeRestrict_surjective hS
    set ι : ↥XI →* ↥(inner S) :=
      (X.subtype.comp XI.subtype).codRestrict (inner S) (fun x => x.2) with hι
    have hιi : Function.Injective ι := by
      intro x y hxy
      have h1 := congrArg (fun z : ↥(inner S) => (z : MulAut S)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Sec16.KSL3PiNoSzProof.false_of_surjective (noSzSection_of_injective ι hιi hI) _ hsurj
      hSz

theorem noSzSection_alt6 :
    NoSzSection (alternatingGroup (Fin 6)) := by
  have h := Item148HJ.card_alternatingGroup_six
  refine noSzSection_of_card ?_ ?_ <;> rw [h] <;> norm_num

theorem noSzSection_mulAut_alt6 :
    NoSzSection (MulAut (alternatingGroup (Fin 6))) := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) := KFacts.KP7.finite_mulAut _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : ¬ 5 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
    intro h5
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
    rw [hk] at h5
    have h52 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
    omega
  exact noSzSection_mulAut_of_outer (S := alternatingGroup (Fin 6)) noSzSection_alt6 h5

theorem noSzSection_on :
    NoSzSection CFSG.Blueprint.NativeSporadic.ON := by
  have : Finite CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.fam_on_simplicity.1
  have h := CFSG.Sporadic.ON.card_ON
  refine noSzSection_of_card ?_ ?_ <;> rw [h]
  · omega
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num

theorem noSzSection_mulAut_on :
    NoSzSection (MulAut CFSG.Blueprint.NativeSporadic.ON) := by
  have : Finite CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.fam_on_simplicity.1
  have h5 : ¬ 5 ∣ Nat.card (Outer CFSG.Blueprint.NativeSporadic.ON) := by
    intro h5
    rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent 5 (by norm_num)
      h5 with h | h <;> omega
  exact noSzSection_mulAut_of_outer (S := CFSG.Blueprint.NativeSporadic.ON) noSzSection_on h5

theorem noSzSection_mulAut_of_isTripleCover {Γ S : Type} [Group Γ] [Group S]
    [Group.IsPerfect Γ] (hT : Sec4.IsTripleCover Γ S) (hS : NoSzSection (MulAut S)) :
    NoSzSection (MulAut Γ) := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  exact noSzSection_of_injective _
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Γ)
    (noSzSection_mulAut_of_mulEquiv e hS)

end NoSz

section Action

variable {J Γ : Type} [Group J] [Group Γ]

@[expose] noncomputable def restrictHom (ρ : J →* MulAut Γ) (W : Subgroup Γ)
    (hW : ∀ j, W.map (ρ j).toMonoidHom = W) : J →* MulAut ↥W where
  toFun j := ((ρ j).subgroupMap W).trans (MulEquiv.subgroupCongr (hW j))
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (ρ 1) (x : Γ) = (x : Γ)
    rw [map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (ρ (a * b)) (x : Γ) = ρ a (ρ b x)
    rw [map_mul]
    rfl

theorem coe_restrictHom_apply (ρ : J →* MulAut Γ) (W : Subgroup Γ)
    (hW : ∀ j, W.map (ρ j).toMonoidHom = W) (j : J) (x : ↥W) :
    ((restrictHom ρ W hW j x : ↥W) : Γ) = ρ j x :=
  rfl

theorem mul_inv_mem_centerIn [Finite J] [Group.IsPerfect J]
    {θ : Subgroup J} [θ.Normal] (hθ : Group.IsSolvable θ) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ θ) 2 n) (ρ : J →* MulAut Γ) (W : Subgroup Γ)
    (hW : ∀ j, W.map (ρ j).toMonoidHom = W) (hTW : Sec4.IsTripleCover ↥W (alternatingGroup (Fin 6)))
    (j : J) {y : Γ} (hy : y ∈ W) : ρ j y * y⁻¹ ∈ Item148PtRes.centerIn W := by
  obtain ⟨-, ⟨eW⟩⟩ := hTW
  set χ : J →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr eW).toMonoidHom.comp
      ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥W).comp
        (restrictHom ρ W hW)) with hχdef
  have hχ : χ.ker = ⊤ := Sec16.ker_eq_top_of_not_suzukiModel_section hθ hSz
    (fun X N _ => noSzSection_mulAut_alt6 X N 2 n) χ
  have hj : χ j = 1 := by
    rw [← MonoidHom.mem_ker, hχ]
    exact Subgroup.mem_top j
  have hj' : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥W
      (restrictHom ρ W hW j) = 1 := by
    apply (MulAut.congr eW).injective
    rw [map_one]
    exact hj
  have h2 := congrArg
    (fun σ : MulAut (↥W ⧸ Subgroup.center ↥W) =>
      σ (QuotientGroup.mk' (Subgroup.center ↥W) ⟨y, hy⟩)) hj'
  change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
      (restrictHom ρ W hW j) (QuotientGroup.mk' (Subgroup.center ↥W) ⟨y, hy⟩) =
    QuotientGroup.mk' (Subgroup.center ↥W) ⟨y, hy⟩ at h2
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  have h2' : (⟨y, hy⟩ : ↥W)⁻¹ * restrictHom ρ W hW j ⟨y, hy⟩ ∈ Subgroup.center ↥W := by
    have h4 := Subgroup.inv_mem _ h2
    rwa [mul_inv_rev, inv_inv] at h4
  have h3 : (restrictHom ρ W hW j ⟨y, hy⟩) * (⟨y, hy⟩ : ↥W)⁻¹ ∈ Subgroup.center ↥W :=
    (Subgroup.center ↥W).normal_of_characteristic.mem_comm h2'
  refine Item148PtRes.mem_centerIn_iff.mpr ⟨W.mul_mem (by
    rw [← coe_restrictHom_apply ρ W hW j ⟨y, hy⟩]
    exact (restrictHom ρ W hW j ⟨y, hy⟩).2) (W.inv_mem hy), ?_⟩
  convert h3 using 1
  exact Subtype.ext rfl

theorem ker_eq_top_of_isCentralProductA6Covers [Finite J]
    [Group.IsPerfect J] [Finite Γ] [Group.IsPerfect Γ] {θ : Subgroup J} [θ.Normal]
    (hθ : Group.IsSolvable θ) {n : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ θ) 2 n)
    (hΓ : IsCentralProductA6Covers Γ) (ρ : J →* MulAut Γ) : ρ.ker = ⊤ := by
  classical
  obtain ⟨U, V, hUn, hVn, hUV, hcomm, h3, hTU, hTV⟩ := hΓ
  have hcU := Item148PtRes.card_eq_of_isTripleCover hTU
  have hcV := Item148PtRes.card_eq_of_isTripleCover hTV
  have hUneV : U ≠ V := by
    intro h
    rw [h, inf_idem, hcV] at h3
    norm_num at h3
  have hmap : ∀ (σ : MulAut Γ) (W : Subgroup Γ), W.Normal → Nat.card W = 1080 →
      W.map σ.toMonoidHom = U ∨ W.map σ.toMonoidHom = V := fun σ W hW hWc =>
    Item148PtRes.eq_or_eq_of_normal hUV hcomm h3 hTU hTV (hW.map _ σ.surjective)
      (by rw [Subgroup.card_map_of_injective σ.injective, hWc, hcU])
  have hinj : ∀ (σ : MulAut Γ) (W W' : Subgroup Γ),
      W.map σ.toMonoidHom = W'.map σ.toMonoidHom → W = W' :=
    fun σ W W' h => Subgroup.map_injective σ.injective h
  have hfixV : ∀ σ : MulAut Γ, U.map σ.toMonoidHom = U → V.map σ.toMonoidHom = V := by
    intro σ hσ
    rcases hmap σ V hVn hcV with h | h
    · exact absurd (hinj σ V U (h.trans hσ.symm)) hUneV.symm
    · exact h
  have hswapV : ∀ σ : MulAut Γ, U.map σ.toMonoidHom ≠ U → V.map σ.toMonoidHom = U := by
    intro σ hσ
    have hσV : U.map σ.toMonoidHom = V := (hmap σ U hUn hcU).resolve_left hσ
    rcases hmap σ V hVn hcV with h | h
    · exact h
    · exact absurd (hinj σ U V (hσV.trans h.symm)) hUneV
  have hmapmul : ∀ (σ τ : MulAut Γ) (W : Subgroup Γ),
      W.map (σ * τ).toMonoidHom = (W.map τ.toMonoidHom).map σ.toMonoidHom := by
    intro σ τ W
    rw [Subgroup.map_map]
    rfl
  let sgn : J → ℤˣ := fun j => if U.map (ρ j).toMonoidHom = U then 1 else -1
  have hsgn : ∀ a b : J, sgn (a * b) = sgn a * sgn b := by
    intro a b
    have hab : U.map (ρ (a * b)).toMonoidHom =
        (U.map (ρ b).toMonoidHom).map (ρ a).toMonoidHom := by
      rw [map_mul]
      exact hmapmul _ _ _
    by_cases hb : U.map (ρ b).toMonoidHom = U
    · by_cases ha : U.map (ρ a).toMonoidHom = U
      · have hab' : U.map (ρ (a * b)).toMonoidHom = U := by rw [hab, hb, ha]
        simp only [sgn, hab', ha, hb, ↓reduceIte, mul_one]
      · have hab' : ¬ U.map (ρ (a * b)).toMonoidHom = U := by
          rw [hab, hb]
          exact ha
        simp only [sgn, hab', ha, hb, ↓reduceIte, mul_one]
    · have hbV : U.map (ρ b).toMonoidHom = V := (hmap _ U hUn hcU).resolve_left hb
      by_cases ha : U.map (ρ a).toMonoidHom = U
      · have hab' : ¬ U.map (ρ (a * b)).toMonoidHom = U := by
          rw [hab, hbV, hfixV _ ha]
          exact hUneV.symm
        simp only [sgn, hab', ha, hb, ↓reduceIte, one_mul]
      · have hab' : U.map (ρ (a * b)).toMonoidHom = U := by rw [hab, hbV, hswapV _ ha]
        simp only [sgn, hab', ha, hb, ↓reduceIte]
        rfl
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative
    (MonoidHom.mk' sgn hsgn)
  have hU : ∀ j, U.map (ρ j).toMonoidHom = U := by
    intro j
    by_contra hj
    have h2 := congrArg (fun φ : J →* ℤˣ => φ j) h1
    simp only [MonoidHom.mk'_apply, MonoidHom.one_apply, sgn, hj, ↓reduceIte] at h2
    exact absurd (congrArg Units.val h2) (by simp)
  have hV : ∀ j, V.map (ρ j).toMonoidHom = V := fun j => hfixV _ (hU j)
  have hcenU : Item148PtRes.centerIn U ≤ Subgroup.center Γ := by
    rw [← Item148PtRes.inf_eq_centerIn_left hcomm h3 hTU.1]
    exact fun x hx => Item148PtRes.mem_center_of_mem_inf hUV hcomm hx
  have hcenV : Item148PtRes.centerIn V ≤ Subgroup.center Γ := by
    rw [← Item148PtRes.inf_eq_centerIn_right hcomm h3 hTV.1]
    exact fun x hx => Item148PtRes.mem_center_of_mem_inf hUV hcomm hx
  have htop := Item148PtRes.top_eq_commutator_sup hUV hcomm
  rw [eq_top_iff]
  intro j _
  rw [MonoidHom.mem_ker]
  have hle : (⊤ : Subgroup Γ) ≤ MonoidHom.eqLocus (ρ j).toMonoidHom (MonoidHom.id Γ) := by
    rw [htop]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Item148PtRes.fixed_of_mem_commutator hcenU
        (fun y hy => mul_inv_mem_centerIn hθ hSz ρ U hU hTU j hy) hx
    · exact Item148PtRes.fixed_of_mem_commutator hcenV
        (fun y hy => mul_inv_mem_centerIn hθ hSz ρ V hV hTV j hy) hx
  ext x
  exact hle (Subgroup.mem_top x)

theorem ker_eq_top_of_types
    [Finite J] [Group.IsPerfect J] [Finite Γ] [Group.IsPerfect Γ] {θ : Subgroup J} [θ.Normal]
    (hθ : Group.IsSolvable θ) {n : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ θ) 2 n)
    (htypes : Sec4.IsTripleCover Γ CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Γ (alternatingGroup (Fin 6)) ∨ IsCentralProductA6Covers Γ)
    (ρ : J →* MulAut Γ) : ρ.ker = ⊤ := by
  rcases htypes with hT | hT | hT
  · exact Sec16.ker_eq_top_of_not_suzukiModel_section hθ hSz
      (fun X N _ => noSzSection_mulAut_of_isTripleCover hT noSzSection_mulAut_on X N 2 n) ρ
  · exact Sec16.ker_eq_top_of_not_suzukiModel_section hθ hSz
      (fun X N _ => noSzSection_mulAut_of_isTripleCover hT noSzSection_mulAut_alt6 X N 2 n) ρ
  · exact ker_eq_top_of_isCentralProductA6Covers hθ hSz hT ρ

end Action

end CFSG.RankThree.PartTwo.Sec17.Proof17Res15
