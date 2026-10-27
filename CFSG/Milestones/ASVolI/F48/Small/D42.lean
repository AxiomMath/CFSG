module

public import CFSG.Milestones.ASVolI.F48.Small.Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F424
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Simple
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Glue
public import CFSG.Milestones.ASVolI.F4K.Main
public import CFSG.Milestones.ASVolI.F48.Id
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Top

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.D4Hex CFSG.LargeExtraspecial.S63

section Parabolics


theorem burnsideF48s_d42_isLieParabolics (hs : IsSimpleGroup D) :
    IsLieParabolics 2 (⊤ : Subgroup D) d4B d4H d4N := by
  have hsyl := d4_sylow
  have hidx : ¬ 2 ∣ d4U.index := by
    have h := hsyl.2.2
    change ¬ 2 ∣ d4U.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hBH : d4B < d4H := lt_of_le_of_ne d4B_le_d4H (Ne.symm d4H_ne_d4B)
  have hBN : d4B < d4N := lt_of_le_of_ne d4B_le_d4N (Ne.symm d4N_ne_d4B)
  have hHtop : d4H ≠ ⊤ := fun h => not_d4N_le_d4H (h ▸ le_top)
  have hNtop : d4N ≠ ⊤ := fun h => not_d4H_le_d4N (h ▸ le_top)
  have hcoH : IsCoatom d4H := by
    refine ⟨hHtop, fun R hR => ?_⟩
    rcases d4_lattice R (hBH.le.trans hR.le) with h | h | h | h
    · rw [h] at hR
      exact absurd hR (lt_asymm hBH)
    · exact absurd h hR.ne'
    · rw [h] at hR
      exact absurd hR.le not_d4H_le_d4N
    · exact h
  have hcoN : IsCoatom d4N := by
    refine ⟨hNtop, fun R hR => ?_⟩
    rcases d4_lattice R (hBN.le.trans hR.le) with h | h | h | h
    · rw [h] at hR
      exact absurd hR (lt_asymm hBN)
    · rw [h] at hR
      exact absurd hR.le not_d4N_le_d4H
    · exact absurd h hR.ne'
    · exact h
  have hco : ∀ Q : Subgroup D, d4B ≤ Q → IsCoatom Q → Q = d4H ∨ Q = d4N := by
    intro Q hQ hQc
    rcases d4_lattice Q hQ with h | h | h | h
    · rw [h] at hQc
      exact absurd (hQc.2 d4H hBH) hHtop
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hQc.1
  exact burnsideF4h_cl_isLieParabolics_top_of hsyl.2.1 hidx (normalizer_d4U_eq_d4B hs)
    d4H_ne_d4N rfl hcoH hcoN hco

end Parabolics

theorem burnsideF48s_d42_mem_iff {X E : Type} [Group X] [Group E] {Gp M : Subgroup E}
    (ε : X ≃* ↥Gp) {Q : Subgroup X} (h : burnsideF48_img ε Q = Gp ⊓ M) (y : ↥Gp) :
    (y : E) ∈ M ↔ ε.symm y ∈ Q := by
  rw [← burnsideF48_mem_img ε Q (ε.symm y), MulEquiv.apply_symm_apply, h]
  exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩

section Chart


theorem burnsideF48s_d42_chart {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 1 (⊤ : Subgroup E) M₁ M₂) (hs : IsSimpleGroup D) :
    ∃ θ : ↥(M₁ ⊔ M₂) ≃* ↥(d4H ⊔ d4N),
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(d4H ⊔ d4N)) : D) ∈ d4H) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(d4H ⊔ d4N)) : D) ∈ d4N) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(d4H ⊔ d4N)) : D) ∈ d4N) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(d4H ⊔ d4N)) : D) ∈ d4H) := by
  haveI : Finite E := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := nonempty_equiv_trialityGroup8 ↥(⊤ : Subgroup E)
    (burnsideF48_lieModel_D4 hyp.model)
  obtain ⟨ε, -, hε⟩ := burnsideF48_identify ε₀.symm (burnsideF48s_d42_isLieParabolics hs) hP
  let θ : ↥(M₁ ⊔ M₂) ≃* ↥(d4H ⊔ d4N) :=
    (MulEquiv.subgroupCongr hyp.gen).trans
      (ε.symm.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr d4H_sup_d4N.symm)))
  refine ⟨θ, ?_⟩
  rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨fun x => burnsideF48s_d42_mem_iff ε h1 (MulEquiv.subgroupCongr hyp.gen x),
      fun x => burnsideF48s_d42_mem_iff ε h2 (MulEquiv.subgroupCongr hyp.gen x)⟩
  · exact Or.inr ⟨fun x => burnsideF48s_d42_mem_iff ε h2 (MulEquiv.subgroupCongr hyp.gen x),
      fun x => burnsideF48s_d42_mem_iff ε h1 (MulEquiv.subgroupCongr hyp.gen x)⟩

end Chart

section Match


theorem burnsideF48s_d42_match (hs : IsSimpleGroup D) : burnsideF48s_Match d4H d4N 6 :=
  burnsideF48s_match_of_qe fun Y _ _ β hβ hs' =>
    (d4Geom.d4F48 hs d4_titsModel d4_hpoly Y β hβ hs').2 rfl

end Match

section Main


theorem burnsideF48s_d42_small_top (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .D4tw 2 1 Gp M₁ M₂) (hGp : Gp = ⊤) :
    ChF.F48Concl .D4tw 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hs : IsSimpleGroup D := d4_isSimpleGroup (D' := ↥Gp) (burnsideF48_lieModel_D4 hyp.model)
  subst hGp
  obtain ⟨θ, hθ⟩ := burnsideF48s_d42_chart hyp hs
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .D4tw 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs'
  have h13 := (burnside_as_F_4_13_of h45 h46 .D4tw 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs').2
  rw [card_G0] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; exact Nat.card_pos.ne')
  exact burnsideF48s_qe_of_match_or (burnsideF48s_d42_match hs) θ hθ β hβ hs'

end Main

section ConjHom

variable {G X : Type} [Group G] [Group X]

@[expose] noncomputable def burnsideF48s_d42_conjHom (R : Subgroup G) [R.Normal] (e : ↥R ≃* X) :
    G →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem burnsideF48s_d42_conjHom_apply (R : Subgroup G) [R.Normal] (e : ↥R ≃* X) (g : G)
    (x : X) :
    ((e.symm (burnsideF48s_d42_conjHom R e g x) : ↥R) : G) = g * (e.symm x : G) * g⁻¹ := by
  show ((e.symm (e (MulAut.conjNormal g (e.symm x))) : ↥R) : G) = _
  rw [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]

theorem burnsideF48s_d42_conjHom_injective (R : Subgroup G) [R.Normal] (e : ↥R ≃* X)
    (hR : Subgroup.centralizer (R : Set G) = ⊥) :
    Function.Injective (burnsideF48s_d42_conjHom R e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := burnsideF48s_d42_conjHom_apply R e g (e ⟨r, hr⟩)
    rw [hg, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : g * r * g⁻¹ = r := h1.symm
    calc r * g = (g * r * g⁻¹) * g := by rw [h2]
      _ = g * r := by group
  rw [hR] at hc
  exact Subgroup.mem_bot.1 hc

theorem burnsideF48s_d42_nonempty_equiv [Finite (MulAut X)] (R : Subgroup G) [R.Normal]
    (e : ↥R ≃* X) (hR : Subgroup.centralizer (R : Set G) = ⊥)
    (hcard : Nat.card (MulAut X) ≤ Nat.card G) : Nonempty (G ≃* MulAut X) :=
  ⟨MulEquiv.ofBijective _
    ((burnsideF48s_d42_conjHom_injective R e hR).bijective_of_nat_card_le hcard)⟩

end ConjHom

theorem burnsideF48s_d42_card_E (hcA : Nat.card (MulAut D) = 3 * Nat.card D) {E : Type}
    [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal] (ε : D ≃* ↥Gp)
    (hcent : Subgroup.centralizer (Gp : Set E) = ⊥) (hGp : Gp ≠ ⊤) :
    Nat.card E = Nat.card (MulAut D) := by
  haveI : Finite D := Finite.of_equiv ↥Gp ε.symm.toEquiv
  have hinj := burnsideF48s_d42_conjHom_injective Gp ε.symm hcent
  have h1 : Nat.card E ∣ Nat.card (MulAut D) := by
    have := Subgroup.card_subgroup_dvd_card (burnsideF48s_d42_conjHom Gp ε.symm).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at this
  have h2 : Nat.card Gp * Gp.index = Nat.card E := Subgroup.card_mul_index Gp
  have h3 : Nat.card Gp = Nat.card D := (Nat.card_congr ε.toEquiv).symm
  rw [hcA, ← h2, h3, mul_comm 3 (Nat.card D)] at h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h4 : Gp.index ∣ 3 := (Nat.mul_dvd_mul_iff_left hpos).1 h1
  rcases (Nat.dvd_prime Nat.prime_three).1 h4 with h | h
  · exact absurd (Subgroup.index_eq_one.1 h) hGp
  · rw [← h2, h3, h, hcA, mul_comm]

theorem burnsideF48s_d42_mem_autStab_iff {E X : Type} [Group E] [Group X]
    {Gp M₁ M₂ M : Subgroup E} [Gp.Normal] (ε : X ≃* ↥Gp) {Q : Subgroup X}
    (hQ : burnsideF48_img ε Q = Gp ⊓ M)
    (hself : ∀ g : X, (∀ x, x ∈ Q ↔ g * x * g⁻¹ ∈ Q) → g ∈ Q)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) (hM : M₁ ⊓ M₂ ≤ M) (e : E) :
    e ∈ M ↔ burnsideF48s_d42_conjHom Gp ε.symm e ∈ autStab Q := by
  have hQx : ∀ x : X, x ∈ Q ↔ ((ε x : ↥Gp) : E) ∈ M := fun x => by
    rw [burnsideF48s_d42_mem_iff ε hQ (ε x), MulEquiv.symm_apply_apply]
  have hval : ∀ (g : E) (x : X), ((ε (burnsideF48s_d42_conjHom Gp ε.symm g x) : ↥Gp) : E) =
      g * (ε x : E) * g⁻¹ := fun g x => burnsideF48s_d42_conjHom_apply Gp ε.symm g x
  have hconj : ∀ {m : E}, m ∈ M → ∀ y : E, y ∈ M ↔ m * y * m⁻¹ ∈ M := by
    intro m hm y
    constructor
    · intro hy
      exact M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)
    · intro hy
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hy) hm
      simpa [mul_assoc] using this
  have hstab : burnsideF48s_d42_conjHom Gp ε.symm e ∈ autStab Q ↔
      ∀ x : X, ((ε x : ↥Gp) : E) ∈ M ↔ e * (ε x : E) * e⁻¹ ∈ M := by
    show (∀ x : X, x ∈ Q ↔ burnsideF48s_d42_conjHom Gp ε.symm e x ∈ Q) ↔ _
    refine forall_congr' fun x => ?_
    rw [hQx x, hQx, hval]
  rw [hstab]
  constructor
  · intro he x
    exact hconj he _
  · intro H
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
    have hhM : h ∈ M := hM hh
    have hn' : ∀ x : X, ((ε x : ↥Gp) : E) ∈ M ↔ n * (ε x : E) * n⁻¹ ∈ M := by
      intro x
      have hy : h⁻¹ * (ε x : E) * h ∈ Gp := by
        have := (inferInstance : Gp.Normal).conj_mem _ (ε x).2 h⁻¹
        simpa using this
      obtain ⟨x', hx'⟩ : ∃ x' : X, ((ε x' : ↥Gp) : E) = h⁻¹ * (ε x : E) * h :=
        ⟨ε.symm ⟨_, hy⟩, by simp⟩
      have e1 := H x'
      rw [hx'] at e1
      have e2 : n * h * (h⁻¹ * (ε x : E) * h) * (n * h)⁻¹ = n * (ε x : E) * n⁻¹ := by group
      rw [e2] at e1
      have e3 : ((ε x : ↥Gp) : E) ∈ M ↔ h⁻¹ * (ε x : E) * h ∈ M := by
        simpa using hconj (M.inv_mem hhM) (ε x : E)
      exact e3.trans e1
    have hg : ε.symm ⟨n, hn⟩ ∈ Q := by
      refine hself _ fun x => ?_
      rw [hQx x, hQx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hn' x
    have hnM : n ∈ M := by
      have := (hQx _).1 hg
      simpa using this
    exact M.mul_mem hnM hhM

@[expose] def burnsideF48s_d42_IsoProp {X : Type} [Group X] (A B : Subgroup X) (m : ℕ) (T : Type)
    [Group T] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : (RankTwoAmalgam.ofSubgroups A B).Completion Y),
    β.IsFaithful → β.IsSmall m → Nat.card Y = Nat.card T → Nonempty (Y ≃* T)

theorem burnsideF48s_d42_isoProp_swap {X : Type} [Group X] {A B : Subgroup X} {m : ℕ} {T : Type}
    [Group T] (h : burnsideF48s_d42_IsoProp A B m T) : burnsideF48s_d42_IsoProp B A m T := by
  intro Y _ _ β hβ hs hc
  exact h Y (burnsideF48s_swapC β) (burnsideF48s_swapC_isFaithful hβ)
    (burnsideF48s_swapC_isSmall hs) hc

theorem burnsideF48s_d42_iso_of_isoProp {E X : Type} [Group E] [Group X] {M₁ M₂ : Subgroup E}
    {A B : Subgroup X} {m : ℕ} {T : Type} [Group T] (hP : burnsideF48s_d42_IsoProp A B m T)
    (θ : ↥(M₁ ⊔ M₂) ≃* ↥(A ⊔ B))
    (h1 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A)
    (h2 : ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B)
    {Y : Type} [Group Y] [Finite Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall m)
    (hc : Nat.card Y = Nat.card T) : Nonempty (Y ≃* T) :=
  hP Y (burnsideF48_comap (burnsideF48_isoSymm (burnsideF48s_amalIsoOf θ h1 h2)) β)
    ((burnsideF48_comap_isFaithful_iff _ β).2 hβ) ((burnsideF48_comap_isSmall_iff _ β m).2 hs) hc

theorem burnsideF48s_d42_iso_of_isoProp_or {E X : Type} [Group E] [Group X]
    {M₁ M₂ : Subgroup E} {A B : Subgroup X} {m : ℕ} {T : Type} [Group T]
    (hP : burnsideF48s_d42_IsoProp A B m T) (θ : ↥(M₁ ⊔ M₂) ≃* ↥(A ⊔ B))
    (hθ : ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ B) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔ ((θ x : ↥(A ⊔ B)) : X) ∈ A))
    {Y : Type} [Group Y] [Finite Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall m)
    (hc : Nat.card Y = Nat.card T) : Nonempty (Y ≃* T) := by
  rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF48s_d42_iso_of_isoProp hP θ h1 h2 β hβ hs hc
  · exact burnsideF48s_d42_iso_of_isoProp (burnsideF48s_d42_isoProp_swap hP)
      (θ.trans (MulEquiv.subgroupCongr (sup_comm A B))) h1 h2 β hβ hs hc

section D3


theorem burnsideF48s_d42_isoProp_d3 {D' : Type} [Group D']
    (hD' : IsLieOverTwo .trialityD4 0 1 D') :
    burnsideF48s_d42_IsoProp (autStab d4H) (autStab d4N) 6 (MulAut D) := by
  have hs : IsSimpleGroup D := d4_isSimpleGroup hD'
  obtain ⟨hcA, hinj⟩ := d4_card_aut hD'
  have hK := d3_K3_eq_top hD'
  haveI : Finite D := finite_D
  haveI : Finite (MulAut D) := Nat.finite_of_card_ne_zero (by
    rw [hcA]
    exact Nat.mul_ne_zero (by norm_num) Nat.card_pos.ne')
  let eN : ↥d3Setting.N ≃* D :=
    (MulEquiv.subgroupCongr (d3_N_eq hK)).trans
      ((Subgroup.equivMapOfInjective _ _ (d3Theta hK).injective).symm.trans
        (MonoidHom.ofInjective hinj).symm)
  intro Y _ _ β hβ hsm hc
  obtain ⟨⟨Ġ, hĠ, β', -, ⟨φ, -⟩, hext⟩, -⟩ :=
    d3F48 hD' (d4_hZH hs) (d4_hNN hs) hs Y β hβ hsm
  obtain ⟨ν, hνinj, hνnorm, hνcent, -⟩ := hext
  haveI := hνnorm
  let eR : ↥ν.range ≃* D := (MonoidHom.ofInjective hνinj).symm.trans eN
  obtain ⟨χ⟩ := burnsideF48s_d42_nonempty_equiv ν.range eR hνcent
    (le_of_eq (by rw [← hc]; exact Nat.card_congr φ.toEquiv))
  exact ⟨φ.trans χ⟩

end D3

section Ext


theorem burnsideF48s_d42_small_ext (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .D4tw 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    ChF.F48Concl .D4tw 2 1 Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  haveI : Gp.Normal := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hD' : IsLieOverTwo .trialityD4 0 1 ↥Gp := burnsideF48_lieModel_D4 hyp.model
  have hs : IsSimpleGroup D := d4_isSimpleGroup hD'
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := nonempty_equiv_trialityGroup8 ↥Gp hD'
  obtain ⟨ε, -, hε⟩ := burnsideF48_identify ε₀.symm (burnsideF48s_d42_isLieParabolics hs) hP
  obtain ⟨hcA, -⟩ := d4_card_aut hD'
  have hcardE := burnsideF48s_d42_card_E hcA ε hyp.centralizer_trivial hGp
  have hinj := burnsideF48s_d42_conjHom_injective Gp ε.symm hyp.centralizer_trivial
  haveI : Finite (MulAut D) := Nat.finite_of_card_ne_zero (by
    rw [← hcardE]
    exact Nat.card_pos.ne')
  let cE : E ≃* MulAut D := MulEquiv.ofBijective _ (hinj.bijective_of_nat_card_le hcardE.ge)
  have hK := d3_K3_eq_top hD'
  let θ : ↥(M₁ ⊔ M₂) ≃* ↥(autStab d4H ⊔ autStab d4N) :=
    (MulEquiv.subgroupCongr hyp.gen).trans (Subgroup.topEquiv.trans
      (cE.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm))))
  have hθ : ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(autStab d4H ⊔ autStab d4N)) : MulAut D) ∈ autStab d4H) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(autStab d4H ⊔ autStab d4N)) : MulAut D) ∈ autStab d4N) ∨
      ((∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₁ ↔
          ((θ x : ↥(autStab d4H ⊔ autStab d4N)) : MulAut D) ∈ autStab d4N) ∧
        ∀ x : ↥(M₁ ⊔ M₂), (x : E) ∈ M₂ ↔
          ((θ x : ↥(autStab d4H ⊔ autStab d4N)) : MulAut D) ∈ autStab d4H) := by
    rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨fun x =>
        burnsideF48s_d42_mem_autStab_iff ε h1 (d4_hHH hs) hyp.split inf_le_left (x : E),
        fun x => burnsideF48s_d42_mem_autStab_iff ε h2 (d4_hNN hs) hyp.split inf_le_right (x : E)⟩
    · exact Or.inr ⟨fun x =>
        burnsideF48s_d42_mem_autStab_iff ε h2 (d4_hNN hs) hyp.split inf_le_left (x : E),
        fun x => burnsideF48s_d42_mem_autStab_iff ε h1 (d4_hHH hs) hyp.split inf_le_right (x : E)⟩
  refine ⟨fun Y _ β hβ hsm => ?_, fun h => absurd h hGp⟩
  have h13 := (burnside_as_F_4_13_of h45 h46 .D4tw 2 1 E Gp M₁ M₂ hyp Y β hβ hsm).2
  rw [card_G0] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; exact Nat.card_pos.ne')
  obtain ⟨χ⟩ := burnsideF48s_d42_iso_of_isoProp_or (burnsideF48s_d42_isoProp_d3 hD') θ hθ β hβ
    hsm (h13.trans hcardE)
  let e : β.G0 ≃* E := (burnsideF48_G0Equiv β).trans (χ.trans cE.symm)
  exact ⟨Y, inferInstance, β, Amalgam.Completion.IsEquivalent.refl _,
    burnsideF48_isLieExtGroup_of_equiv e.symm hext, ⟨MulEquiv.refl _⟩⟩

theorem burnsideF48s_d42_small (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .D4tw 2 1 Gp M₁ M₂) :
    ChF.F48Concl .D4tw 2 1 Gp M₁ M₂ := by
  by_cases hGp : Gp = ⊤
  · exact burnsideF48s_d42_small_top h45 h46 hyp hGp
  · exact burnsideF48s_d42_small_ext h45 h46 hyp hGp

end Ext

end CFSG.ASVolI
