module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNA
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211Kv

section Layer

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem layer_coe_layer_eq_top (Y : Type) [Group Y] : CFSG.layer ↥(CFSG.layer Y) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

omit [Finite Y] in
theorem center_layer_eq_bot (hY : CFSG.solvableRadical Y = ⊥) :
    (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype = ⊥ :=
  CFSG.WholeGroup.center_layer_eq_bot_of_solvableRadical_eq_bot hY

theorem center_component_eq_bot (hY : CFSG.solvableRadical Y = ⊥) {S : Subgroup Y}
    (hS : CFSG.IsComponent S) : Subgroup.center ↥S = ⊥ := by
  have h1 := CFSG.LocalCores.center_component_le_center_layer hS
  rw [center_layer_eq_bot hY, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp h1

theorem inf_eq_bot_of_ne (hY : CFSG.solvableRadical Y = ⊥) {S T : Subgroup Y}
    (hS : CFSG.IsComponent S) (hT : CFSG.IsComponent T) (hne : S ≠ T) : S ⊓ T = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute hS hT with h | h
  · exact absurd h hne
  rw [eq_bot_iff]
  intro x hx
  have hST := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hxc : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hST s.2) x hx.2).symm
  rw [center_component_eq_bot hY hS, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

theorem false_of_two_nine (hY : CFSG.solvableRadical Y = ⊥)
    (hrk : CFSG.Open.pRank 3 (CFSG.layer Y) ≤ 2) {S T : Subgroup Y}
    (hS : CFSG.IsComponent S) (hT : CFSG.IsComponent T) (hne : S ≠ T) {A₀ B₀ : Type}
    [Group A₀] [Group B₀] (hAc : ∀ a b : A₀, a * b = b * a) (hA3 : ∀ a : A₀, a ^ 3 = 1)
    (hcA : Nat.card A₀ = 9) (hBc : ∀ a b : B₀, a * b = b * a) (hB3 : ∀ b : B₀, b ^ 3 = 1)
    (hcB : Nat.card B₀ = 9) (f : A₀ →* Y) (hf : Function.Injective f) (hfS : f.range ≤ S)
    (g : B₀ →* Y) (hg : Function.Injective g) (hgT : g.range ≤ T) : False := by
  have hST := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute hS hT).resolve_left hne)
  have hcomm : ∀ (a : A₀) (b : B₀), Commute (f a) (g b) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (hST (hfS ⟨a, rfl⟩)) (g b) (hgT ⟨b, rfl⟩)).symm
  set F := f.noncommCoprod g hcomm with hF
  have hinj : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [hF, MonoidHom.noncommCoprod_apply] at h
    have h1 : (f a')⁻¹ * f a = g b' * (g b)⁻¹ := by
      calc (f a')⁻¹ * f a = (f a')⁻¹ * (f a * g b) * (g b)⁻¹ := by group
        _ = (f a')⁻¹ * (f a' * g b') * (g b)⁻¹ := by rw [h]
        _ = g b' * (g b)⁻¹ := by group
    have hm : (f a')⁻¹ * f a ∈ S ⊓ T := ⟨hfS ⟨a'⁻¹ * a, by simp⟩,
      h1 ▸ hgT ⟨b' * b⁻¹, by simp⟩⟩
    rw [inf_eq_bot_of_ne hY hS hT hne, Subgroup.mem_bot] at hm
    have h2 : g b' * (g b)⁻¹ = 1 := h1 ▸ hm
    rw [hf (inv_mul_eq_one.mp hm).symm, hg (mul_inv_eq_one.mp h2).symm]
  have h4 := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (A := A₀ × B₀) (k := 4)
    (fun x y => Prod.ext (hAc x.1 y.1) (hBc x.2 y.2))
    (fun x => Prod.ext (hA3 x.1) (hB3 x.2))
    (by rw [Nat.card_prod, hcA, hcB]; norm_num) F hinj (H := CFSG.layer Y) (by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (CFSG.layer Y).mul_mem (CFSG.LocalCores.component_le_layer hS (hfS ⟨a, rfl⟩))
        (CFSG.LocalCores.component_le_layer hT (hgT ⟨b, rfl⟩)))
  omega

theorem layer_eq_sup_others {S : Subgroup Y} (hS : CFSG.IsComponent S) :
    sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} ≤ Subgroup.centralizer (S : Set Y) ∧
      CFSG.layer Y = S ⊔ sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} :=
  CFSG.WholeGroup.layer_eq_sup_others hS

theorem exists_proj (hY : CFSG.solvableRadical Y = ⊥) {S A : Subgroup Y}
    (hS : CFSG.IsComponent S) (hAE : A ≤ CFSG.layer Y)
    (hAC : A ⊓ Subgroup.centralizer (S : Set Y) = ⊥) :
    ∃ φ : ↥A →* Y, Function.Injective φ ∧ φ.range ≤ S := by
  set E' : Subgroup Y := sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} with hE'
  obtain ⟨hE'C, hlayer⟩ := layer_eq_sup_others hS
  have hSL : S ≤ CFSG.layer Y := CFSG.LocalCores.component_le_layer hS
  have hE'L : E' ≤ CFSG.layer Y := hlayer ▸ le_sup_right
  have hLN : CFSG.layer Y ≤ Subgroup.normalizer (E' : Set Y) := by
    rw [hlayer]
    refine sup_le (fun s hs => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.le_centralizer_iff.mp hE'C hs)
  have hN : (E'.subgroupOf (CFSG.layer Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE'L).mpr hLN
  set q := QuotientGroup.mk' (E'.subgroupOf (CFSG.layer Y)) with hq
  set ψ : ↥S →* ↥(CFSG.layer Y) ⧸ E'.subgroupOf (CFSG.layer Y) :=
    q.comp (Subgroup.inclusion hSL) with hψ
  have hSE : S ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hE'C hx.2) s s.2)
    rw [center_component_eq_bot hY hS, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    rw [hψ, MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hs
    have h1 : (s : Y) ∈ S ⊓ E' := ⟨s.2, hs⟩
    rw [hSE, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hx : (x : Y) ∈ ((S ⊔ E' : Subgroup Y) : Set Y) := by
      rw [← hlayer]
      exact x.2
    rw [A4.coe_sup_eq_mul_of_mul_comm (Sec1211Nq.mul_comm_of_le_normalizer
      (hE'C.trans (Subgroup.centralizer_le_normalizer _)))] at hx
    obtain ⟨s, hs, e, he, hse⟩ := hx
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (s : Y)⁻¹ * x ∈ E'
    rw [← hse]
    simpa using he
  set eS := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩ with heS
  set φ₀ : ↥A →* ↥S := eS.symm.toMonoidHom.comp (q.comp (Subgroup.inclusion hAE)) with hφ₀
  refine ⟨S.subtype.comp φ₀, ?_, ?_⟩
  · refine S.subtype_injective.comp ?_
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hφ₀, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
    have h1 : (a : Y) ∈ A ⊓ Subgroup.centralizer (S : Set Y) := ⟨a.2, hE'C ha⟩
    rw [hAC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  · rintro _ ⟨a, rfl⟩
    exact (φ₀ a).2

theorem le_of_commute_others (hY : CFSG.solvableRadical Y = ⊥) {S B : Subgroup Y}
    (hS : CFSG.IsComponent S) (hBE : B ≤ CFSG.layer Y)
    (hB : ∀ T : Subgroup Y, CFSG.IsComponent T → T ≠ S → ⁅T, B⁆ = ⊥) : B ≤ S := by
  set E' : Subgroup Y := sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} with hE'
  obtain ⟨hE'C, hlayer⟩ := layer_eq_sup_others hS
  have hBC : B ≤ Subgroup.centralizer (E' : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun T hT =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hB T hT.1 hT.2)
  intro b hb
  have hb' : b ∈ ((S ⊔ E' : Subgroup Y) : Set Y) := by
    rw [← hlayer]
    exact hBE hb
  rw [A4.coe_sup_eq_mul_of_mul_comm (Sec1211Nq.mul_comm_of_le_normalizer
    (hE'C.trans (Subgroup.centralizer_le_normalizer _)))] at hb'
  obtain ⟨s, hs, e, he, rfl⟩ := hb'
  have he1 : e = 1 := by
    have heZ : e ∈ (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype := by
      have hE'L : E' ≤ CFSG.layer Y := hlayer ▸ le_sup_right
      refine (CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hE'L he, ?_⟩
      rw [hlayer, Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ ((S ⊔ E' : Subgroup Y) : Set Y) := hy
      rw [A4.coe_sup_eq_mul_of_mul_comm (Sec1211Nq.mul_comm_of_le_normalizer
        (hE'C.trans (Subgroup.centralizer_le_normalizer _)))] at hy'
      obtain ⟨s', hs', e', he', rfl⟩ := hy'
      have h1 : s' * e = e * s' := (Subgroup.mem_centralizer_iff.mp (hE'C he) s' hs')
      have hes : e = s⁻¹ * (s * e) := by group
      have h2 : e' * e = e * e' := by
        have hb2 := Subgroup.mem_centralizer_iff.mp (hBC hb) e' he'
        have hs2 := Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer_iff.mp hE'C hs) e' he'
        rw [hes]
        calc e' * (s⁻¹ * (s * e)) = (e' * s⁻¹) * (s * e) := by group
          _ = (s⁻¹ * e') * (s * e) := by
            rw [show e' * s⁻¹ = s⁻¹ * e' from by
              calc e' * s⁻¹ = s⁻¹ * (s * e') * s⁻¹ := by group
                _ = s⁻¹ * (e' * s) * s⁻¹ := by rw [hs2]
                _ = s⁻¹ * e' := by group]
          _ = s⁻¹ * (e' * (s * e)) := by group
          _ = s⁻¹ * ((s * e) * e') := by rw [hb2]
          _ = s⁻¹ * (s * e) * e' := by group
      calc s' * e' * e = s' * (e' * e) := by group
        _ = s' * (e * e') := by rw [h2]
        _ = (s' * e) * e' := by group
        _ = (e * s') * e' := by rw [h1]
        _ = e * (s' * e') := by group
    rw [center_layer_eq_bot hY, Subgroup.mem_bot] at heZ
    exact heZ
  show s * e ∈ S
  rw [he1, mul_one]
  exact hs

end Layer

section Main

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_two_three {Γ : Type} [Group Γ] {x : Γ} {e : ℕ} (h2 : x ^ 2 ^ e = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one h2
  have h1' := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime (2 ^ e) 3 := Nat.Coprime.pow_left e (by norm_num)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h1'
  exact orderOf_eq_one_iff.mp this

theorem exists_normal_cComp_ge (hA21 : AsA21SQTKSection) (hX : SQTKGroup X) {B A : Subgroup X}
    (hBp : ⁅B, B⁆ = B) (hBE : B ≤ cCompSpan (⊤ : Subgroup X))
    (hBn : ∀ N : Subgroup X, N ≤ B → B ≤ Subgroup.normalizer (N : Set X) →
      N = B ∨ IsPGroup 2 ↥N)
    (hAB : A ≤ B) (hA : IsElemAbelian 3 A) (hcA : Nat.card A = 9) :
    ∃ K ∈ cComp (⊤ : Subgroup X), B ≤ K ∧ Subgroup.normalizer (K : Set X) = ⊤ := by
  classical
  set R := CFSG.solvableRadical X with hRdef
  have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  set π := QuotientGroup.mk' R with hπ
  have hY : CFSG.solvableRadical (X ⧸ R) = ⊥ := A3.solvableRadical_quotient_eq_bot X
  set E := CFSG.layer (X ⧸ R) with hEdef
  have hEmap : (cCompSpan (⊤ : Subgroup X)).map π = E := map_cCompSpan_eq_layer
  have hrk : CFSG.Open.pRank 3 E ≤ 2 := by
    have hsq : SQTKGroup ↥E := by
      refine hA21 X hX (E.comap π) ↥E
        ((π.comp (E.comap π).subtype).codRestrict E fun x => x.2) ?_ ⊤ ?_ ?_
      · intro y
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R (y : X ⧸ R)
        refine ⟨⟨x, show π x ∈ E by rw [hx]; exact y.2⟩, Subtype.ext ?_⟩
        exact hx
      · exact CFSG.SectionRank.layer_eq_top_of_mulEquiv Subgroup.topEquiv.symm
          (layer_coe_layer_eq_top (X ⧸ R))
      · intro g
        exact ⟨0, @Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top _ _⟩
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hsq.1 3 Nat.prime_three (by norm_num)
  have hBR : IsPGroup 2 ↥(B ⊓ R) := by
    rcases hBn (B ⊓ R) inf_le_left (fun b hb => Subgroup.mem_normalizer_iff.mpr fun x => by
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨B.mul_mem (B.mul_mem hb hx1) (B.inv_mem hb), (inferInstance : R.Normal).conj_mem x hx2 b⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · have := B.mul_mem (B.mul_mem (B.inv_mem hb) hx1) hb
          simpa [mul_assoc] using this
        · have := (inferInstance : R.Normal).conj_mem _ hx2 b⁻¹
          simpa [mul_assoc] using this) with h | h
    · exfalso
      have hBRle : B ≤ R := h ▸ inf_le_right
      have : Group.IsSolvable ↥B :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBRle)
      have hB1 := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hBp
      have hA1 : A = ⊥ := le_bot_iff.mp (hB1 ▸ hAB)
      rw [hA1, Subgroup.card_bot] at hcA
      omega
    · exact h
  have hAR : ∀ a ∈ A, a ∈ R → a = 1 := by
    intro a ha haR
    obtain ⟨e, he⟩ := hBR ⟨a, hAB ha, haR⟩
    exact eq_one_of_two_three (congrArg Subtype.val he) (hA.2 a ha)
  set ι : ↥A →* X ⧸ R := π.comp A.subtype with hι
  have hιi : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro a h1
    rw [hι, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext (hAR a a.2 h1)
  set At := ι.range with hAt
  have hAtE : At ≤ E := by
    rintro _ ⟨a, rfl⟩
    rw [← hEmap]
    exact ⟨a, hBE (hAB a.2), rfl⟩
  have hcAt : Nat.card ↥At = 9 := by
    rw [← hcA]
    exact (Nat.card_congr (MonoidHom.ofInjective hιi).toEquiv).symm
  have hAtc : ∀ x y : ↥At, x * y = y * x := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show ι a * ι b = ι b * ι a
    rw [← map_mul, ← map_mul]
    congr 1
    exact hA.1.is_comm.comm a b
  have hAt3 : ∀ x : ↥At, x ^ 3 = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    show ι a ^ 3 = 1
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]
  set Bt := B.map π with hBt
  have hBtE : Bt ≤ E := hEmap ▸ Subgroup.map_mono hBE
  have hAtBt : At ≤ Bt := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, hAB a.2, rfl⟩
  have hproj : ∀ T : Subgroup (X ⧸ R), CFSG.IsComponent T → ⁅T, Bt⁆ ≠ ⊥ →
      ∃ φ : ↥At →* X ⧸ R, Function.Injective φ ∧ φ.range ≤ T := by
    intro T hT hne
    refine exists_proj hY hT hAtE (eq_bot_iff.mpr fun y hy => ?_)
    obtain ⟨⟨a, rfl⟩, hyC⟩ := hy
    set N := B ⊓ (Subgroup.centralizer (T : Set (X ⧸ R))).comap π with hN
    have hTn : Bt ≤ Subgroup.normalizer (T : Set (X ⧸ R)) :=
      hBtE.trans (CFSG.LocalCores.layer_le_normalizer hT)
    have hNn : B ≤ Subgroup.normalizer (N : Set X) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ g ∈ B, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
        intro g hg x hx
        refine ⟨B.mul_mem (B.mul_mem hg hx.1) (B.inv_mem hg), ?_⟩
        show π (g * x * g⁻¹) ∈ Subgroup.centralizer (T : Set (X ⧸ R))
        rw [map_mul, map_mul, map_inv]
        have hgT : π g ∈ Subgroup.normalizer (T : Set (X ⧸ R)) := hTn ⟨g, hg, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have ht' : (π g)⁻¹ * t * π g ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgT) t).mp ht
          rwa [inv_inv] at this
        have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ ht'
        calc t * (π g * π x * (π g)⁻¹) = π g * (((π g)⁻¹ * t * π g) * π x) * (π g)⁻¹ := by
              group
          _ = π g * (π x * ((π g)⁻¹ * t * π g)) * (π g)⁻¹ := by rw [h1]
          _ = π g * π x * (π g)⁻¹ * t := by group
      intro x
      refine ⟨fun hx => key b hb x hx, fun hx => ?_⟩
      have := key b⁻¹ (B.inv_mem hb) _ hx
      simpa [mul_assoc] using this
    rcases hBn N inf_le_left hNn with h | h
    · exfalso
      apply hne
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← h] at hb
      exact (Subgroup.mem_centralizer_iff.mp hb.2 t ht).symm
    · have ha1 : (a : X) = 1 := by
        obtain ⟨e, he⟩ := h ⟨a, hAB a.2, hyC⟩
        exact eq_one_of_two_three (congrArg Subtype.val he) (hA.2 a a.2)
      have : a = 1 := Subtype.ext ha1
      rw [this, map_one]
      exact Subgroup.one_mem _
  obtain ⟨S₀, hS₀, hS₀ne⟩ : ∃ S₀ : Subgroup (X ⧸ R), CFSG.IsComponent S₀ ∧ ⁅S₀, Bt⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hBtC : Bt ≤ Subgroup.centralizer (E : Set (X ⧸ R)) := by
      rw [Subgroup.le_centralizer_iff]
      exact sSup_le fun T hT => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno T hT)
    have hBt1 : Bt = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyZ : y ∈ (Subgroup.center E).map E.subtype :=
        (CFSG.LocalCores.mem_map_center_iff _).mpr ⟨hBtE hy, hBtC hy⟩
      rwa [center_layer_eq_bot hY] at hyZ
    have : At = ⊥ := le_bot_iff.mp (hBt1 ▸ hAtBt)
    rw [this, Subgroup.card_bot] at hcAt
    omega
  obtain ⟨φ₀, hφ₀, hφ₀S⟩ := hproj S₀ hS₀ hS₀ne
  have huniq : ∀ T : Subgroup (X ⧸ R), CFSG.IsComponent T → T ≠ S₀ → ⁅T, Bt⁆ = ⊥ := by
    intro T hT hTne
    by_contra hne
    obtain ⟨φ, hφ, hφT⟩ := hproj T hT hne
    exact false_of_two_nine hY hrk hS₀ hT (Ne.symm hTne) hAtc hAt3 hcAt hAtc hAt3 hcAt
      φ₀ hφ₀ hφ₀S φ hφ hφT
  have hBtS : Bt ≤ S₀ := le_of_commute_others hY hS₀ hBtE huniq
  have hS₀c : S₀ ∈ cComp (⊤ : Subgroup (X ⧸ R)) := by
    rw [cComp_top_eq_components hY]
    exact hS₀
  rw [← image_cComp_quotient R hRs] at hS₀c
  obtain ⟨K, hK, hKS⟩ := hS₀c
  have hker : Group.IsSolvable ↥π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hRs
  have hRK : R ≤ Subgroup.normalizer (K : Set X) := by
    intro r hr
    have hKr := cComp_map_mulEquiv (MulAut.conj r) hK
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj r).surjective] at hKr
    have hr1 : π r = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hr
    have hπr : ∀ k, π (r * k * r⁻¹) = π k := by
      intro k
      rw [map_mul, map_mul, map_inv, hr1]
      group
    have heq : (K.map (MulAut.conj r).toMonoidHom).map π = K.map π := by
      rw [Subgroup.map_map]
      apply le_antisymm
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨k, hk, (hπr k).symm⟩
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨k, hk, hπr k⟩
    have := map_injOn_cComp_top π hker hKr hK heq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact this
  have hBK : B ≤ K := by
    have hBKR : B ≤ K ⊔ R := by
      have h1 : B ≤ (B.map π).comap π := Subgroup.le_comap_map π B
      refine h1.trans ?_
      rw [show K ⊔ R = (K.map π).comap π by
        rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']]
      exact Subgroup.comap_mono (hKS ▸ hBtS)
    have hKn : (K.subgroupOf (K ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hRK)
    exact (le_perfectCore_of_perfect hBKR hBp).trans
      (perfectCore_le_of_sup_solvable le_sup_left hKn rfl hRs)
  refine ⟨K, hK, hBK, eq_top_iff.mpr fun x _ => ?_⟩
  have hKx := cComp_map_mulEquiv (MulAut.conj x) hK
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective] at hKx
  have hSx : (K.map (MulAut.conj x).toMonoidHom).map π =
      S₀.map (MulAut.conj (π x)).toMonoidHom := by
    rw [← hKS, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hSxc : CFSG.IsComponent (S₀.map (MulAut.conj (π x)).toMonoidHom) := by
    have h1 := map_mem_cComp_top π (QuotientGroup.mk'_surjective R) hker hKx
    rw [hSx, cComp_top_eq_components hY] at h1
    exact h1
  have heq : S₀.map (MulAut.conj (π x)).toMonoidHom = S₀ := by
    by_contra hne
    exact false_of_two_nine hY hrk hS₀ hSxc (Ne.symm hne) hAtc hAt3 hcAt hAtc hAt3 hcAt
      φ₀ hφ₀ hφ₀S ((MulAut.conj (π x)).toMonoidHom.comp φ₀)
      ((MulAut.conj (π x)).injective.comp hφ₀) (by
        rintro _ ⟨a, rfl⟩
        exact ⟨φ₀ a, hφ₀S ⟨a, rfl⟩, rfl⟩)
  have hKeq : K.map (MulAut.conj x).toMonoidHom = K :=
    map_injOn_cComp_top π hker hKx hK (by rw [hSx, heq, hKS])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hKeq

end Main

section Simple

variable {G : Type} [Group G] [Finite G]

theorem eq_or_isPGroup_of_surjective {B N : Subgroup G} (hBp : ⁅B, B⁆ = B) {Q : Type} [Group Q]
    [IsSimpleGroup Q] (f : ↥B →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker)
    (hNB : N ≤ B) (hNn : B ≤ Subgroup.normalizer (N : Set G)) : N = B ∨ IsPGroup 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := N.subgroupOf B with hN₀def
  have hN₀ : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hNn
  have := hN₀.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map f) with h | h
  · right
    intro x
    have hx : (⟨x, hNB x.2⟩ : ↥B) ∈ f.ker := by
      have h1 : f ⟨x, hNB x.2⟩ ∈ N₀.map f := ⟨⟨x, hNB x.2⟩, x.2, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact h1
    obtain ⟨e, he⟩ := hk ⟨_, hx⟩
    refine ⟨e, Subtype.ext ?_⟩
    have := congrArg (fun y : ↥f.ker => ((y : ↥B) : G)) he
    simpa using this
  · left
    have h2 : IsPGroup 2 (↥B ⧸ N₀) := by
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have hb : f b ∈ N₀.map f := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnb⟩ := hb
      have hk' : n⁻¹ * b ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnb, inv_mul_cancel]
      obtain ⟨e, he⟩ := hk ⟨_, hk'⟩
      refine ⟨e, ?_⟩
      have h1 : (QuotientGroup.mk b : ↥B ⧸ N₀) = QuotientGroup.mk (n⁻¹ * b) := by
        rw [QuotientGroup.eq]
        have := hN₀.conj_mem _ (N₀.inv_mem hn) b⁻¹
        simpa [mul_assoc] using this
      rw [h1, ← QuotientGroup.mk_pow]
      have h3 : (n⁻¹ * b) ^ 2 ^ e = 1 := congrArg Subtype.val he
      rw [h3, QuotientGroup.mk_one]
    have hBtop : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = (⊤ : Subgroup ↥B) := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hBp]
    have hperf : ⁅(⊤ : Subgroup (↥B ⧸ N₀)), (⊤ : Subgroup (↥B ⧸ N₀))⁆ =
        (⊤ : Subgroup (↥B ⧸ N₀)) := by
      have h4 := congrArg (Subgroup.map (QuotientGroup.mk' N₀)) hBtop
      rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N₀)] at h4
    have : Group.IsNilpotent (↥B ⧸ N₀) := h2.isNilpotent
    have h5 := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hperf
    apply le_antisymm hNB
    intro b hb
    have h6 : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N₀) ∈ (⊤ : Subgroup (↥B ⧸ N₀)) := Subgroup.mem_top _
    rw [h5, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h6
    exact h6

theorem exists_elemAbelian_nine {B : Subgroup G}
    (f : ↥B →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 ↥f.ker) : ∃ A ≤ B, IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk3 : ¬ 3 ∣ Nat.card ↥f.ker := by
    obtain ⟨e, he⟩ := hk.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hr : 2 ≤ CFSG.Open.pRank 3 B := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_quotient_eq f.ker hk3,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
        ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)))]
    exact R3c.two_le_pRank_three_statedSL_four_two
  obtain ⟨E, hEB, hE, hcE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) B
  have h9 : 3 ^ 2 ∣ Nat.card ↥E := by
    rw [hcE]
    exact Nat.pow_dvd_pow 3 hr
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  have := hE.1
  have hK3 : IsElemAbelian 3 K := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact (this.is_comm.comm (a : ↥E) (b : ↥E))
    · simpa using hE.2 (x : G) x.2
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEB,
    CFSG.SectionRank.isElemAbelian_map hK3 E.subtype, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num

end Simple

end Sec1211Kv

open Sec1211Ns in
theorem lem1211NNKv5_of (h39 : Vol2Native.A39ForSQTKCat) (hA21 : AsA21SQTKSection) :
    Lem1211NNKv5 := by
  intro G _ _ T L V V₁ V₂ β hyp hTL hβ v hv hns hchar
  obtain ⟨S₀⟩ := KGH91.Setting.nonempty hyp
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, hac⟩ := hns
  have hP := KGH91.eq_pairing S₀.hn S₀.C₁ S₀.C₂ S₀.dual hβ.1 hβ.2.1 hβ.2.2.2.2
    ⟨a₀, ha₀, c₀, hc₀, by rw [hac]; exact one_ne_zero⟩ a₀ ha₀ c₀ hc₀
  have S : Sec1211Ns.Setting T L V V₁ V₂ 5 a₀ c₀ :=
    { toSetting := S₀, hTL := hTL, ha₀ := ha₀, hc₀ := hc₀, hns := hP ▸ hac }
  obtain ⟨F⟩ := S.nonempty_frame
  rw [← S.lv_eq_oTwoUpper]
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hHdef
  set Lv := Sec1216Lv.lv L (a₀ * c₀) with hLvdef
  have : IsSimpleGroup G := S.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke
  have hH : pCoreOf 2 H ≠ ⊥ := S.pCoreOf_ne_bot
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian hH
  have h121 : cCompSpan H = perfectCore H := Vol2Native.lemma_1_2_1_one hqtke.1 h39 hH
  have hLvH : Lv ≤ H := Sec1216Lv.lv_le_centralizer L _
  have hLvp : ⁅Lv, Lv⁆ = Lv := Sec1216Lv.lv_perfect L _
  have hLvE : Lv ≤ cCompSpan H := h121 ▸ le_perfectCore_of_perfect hLvH hLvp
  set B := Lv.subgroupOf H with hBdef
  have hBmap : B.map H.subtype = Lv := Subgroup.map_subgroupOf_eq_of_le hLvH
  have hBp : ⁅B, B⁆ = B := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hBmap, hLvp]
  have hspan : cCompSpan H ≤ (cCompSpan (⊤ : Subgroup ↥H)).map H.subtype := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hK)]
    exact Subgroup.map_mono (le_cCompSpan (subgroupOf_mem_cComp hK))
  have hBE : B ≤ cCompSpan (⊤ : Subgroup ↥H) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hspan (hLvE hx)
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  set ψ := Setting.psi F S.lv_le_Xv with hψ
  have hψs : Function.Surjective ψ := Setting.psi_lv_surjective F
  have hψk : IsPGroup 2 ↥ψ.ker := Setting.isPGroup_ker_psi_lv F
  have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  have hBn : ∀ N : Subgroup ↥H, N ≤ B → B ≤ Subgroup.normalizer (N : Set ↥H) →
      N = B ∨ IsPGroup 2 ↥N := by
    intro N hNB hNn
    have hN'B : N.map H.subtype ≤ Lv := hBmap ▸ Subgroup.map_mono hNB
    have hN'n : Lv ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
      intro l hl
      have hlB : (⟨l, hLvH hl⟩ : ↥H) ∈ B := hl
      have h1 := hNn hlB
      rw [Subgroup.mem_normalizer_iff] at h1 ⊢
      intro g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, (h1 x).mp hx, rfl⟩
      · rintro ⟨y, hy, hyg⟩
        have hgH : g ∈ H := by
          have : l⁻¹ * (l * g * l⁻¹) * l ∈ H :=
            H.mul_mem (H.mul_mem (H.inv_mem (hLvH hl)) (hyg ▸ y.2)) (hLvH hl)
          simpa [mul_assoc] using this
        refine ⟨⟨g, hgH⟩, (h1 ⟨g, hgH⟩).mpr ?_, rfl⟩
        have : (⟨l, hLvH hl⟩ * ⟨g, hgH⟩ * (⟨l, hLvH hl⟩ : ↥H)⁻¹ : ↥H) = y :=
          Subtype.ext hyg.symm
        rw [this]
        exact hy
    rcases Sec1211Kv.eq_or_isPGroup_of_surjective hLvp ψ hψs hψk hN'B hN'n with h | h
    · left
      apply Subgroup.map_injective H.subtype_injective
      rw [h, hBmap]
    · right
      exact h.of_injective (Subgroup.equivMapOfInjective N H.subtype
        H.subtype_injective).toMonoidHom (Subgroup.equivMapOfInjective N H.subtype
        H.subtype_injective).injective
  obtain ⟨A, hALv, hA, hcA⟩ := Sec1211Kv.exists_elemAbelian_nine ψ hψs hψk
  have hAH : A ≤ H := hALv.trans hLvH
  have hAmap : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hA'B : A.subgroupOf H ≤ B := fun x hx => hALv hx
  have hcA' : Nat.card ↥(A.subgroupOf H) = 9 := by
    have h1 : Nat.card ↥((A.subgroupOf H).map H.subtype) = Nat.card ↥(A.subgroupOf H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [hAmap] at h1
    rw [← h1, hcA]
  have hA' : IsElemAbelian 3 (A.subgroupOf H) := by
    have hAc := hA.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · show ((a : ↥H) : G) * ((b : ↥H) : G) = ((b : ↥H) : G) * ((a : ↥H) : G)
      exact congrArg Subtype.val (hAc.is_comm.comm ⟨((a : ↥H) : G), a.2⟩ ⟨((b : ↥H) : G), b.2⟩)
    · simpa using hA.2 (x : G) hx
  obtain ⟨K, hK, hBK, hKn⟩ := Sec1211Kv.exists_normal_cComp_ge hA21 hSQ hBp hBE hBn hA'B hA' hcA'
  have hKnorm : K.Normal := Subgroup.normalizer_eq_top_iff.mp hKn
  refine ⟨K.map H.subtype, map_subtype_mem_cComp hK, ?_, fun h hh => ?_⟩
  · rw [← hBmap]
    exact Subgroup.map_mono hBK
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, hKnorm.conj_mem k hk ⟨h, hh⟩, rfl⟩
    · rintro ⟨k, hk, hkg⟩
      have hgH : g ∈ H := by
        have : h⁻¹ * (h * g * h⁻¹) * h ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem hh) (hkg ▸ k.2)) hh
        simpa [mul_assoc] using this
      refine ⟨⟨g, hgH⟩, ?_, rfl⟩
      have h1 := hKnorm.conj_mem k hk (⟨h, hh⟩ : ↥H)⁻¹
      have hkg' : (k : G) = h * g * h⁻¹ := hkg
      have e : ((⟨h, hh⟩ : ↥H)⁻¹ * k * ((⟨h, hh⟩ : ↥H)⁻¹)⁻¹ : ↥H) = ⟨g, hgH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
        rw [hkg']
        group
      rwa [e] at h1

theorem lem1211NotNormal_of_inputs (h331 : Stmt3_3_1)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) (hParab : Lem1211NNParab) (hG2 : Lem1211NNG2)
    (hSL3 : Lem1211NNSL3) (hMod : Lem1211NNMod) : Lem1211NotNormal :=
  lem1211NotNormal_of h331 h129 h36 h37 h38 h39 hC27 hB51 hA21 hParab hG2 hSL3 hMod
    (lem1211NNKv5_of h39 hA21)

end CFSG.Quasithin.H13
