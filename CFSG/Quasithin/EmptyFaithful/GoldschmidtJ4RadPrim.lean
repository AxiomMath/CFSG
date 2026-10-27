module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal

public section

namespace CFSG.Quasithin.J4Rad

open scoped Pointwise
open CFSG.RankThreeEvenClassification.Helpers

theorem index_eq_card_of_abelian_normal {G : Type*} [Group G] [Finite G] {C N : Subgroup G}
    [N.Normal] (hC : IsCoatom C) (hcore : C.normalCore = ⊥) (hNC : ¬ N ≤ C)
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : C.index = Nat.card N := by
  have hsup : N ⊔ C = ⊤ := by
    refine hC.2 _ (lt_of_le_of_ne le_sup_right fun h => hNC ?_)
    rw [h]
    exact le_sup_left
  have hmul : (N : Set G) * (C : Set G) = Set.univ := by
    rw [← Subgroup.normal_mul, hsup]
    exact Subgroup.coe_top
  have hnorm : (N ⊓ C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ ((N : Set G) * (C : Set G)) := by rw [hmul]; trivial
    obtain ⟨n, hn, c, hc, rfl⟩ := Set.mem_mul.mp hg
    have h1 : c * x * c⁻¹ ∈ N ⊓ C :=
      ⟨‹N.Normal›.conj_mem x hx.1 c, C.mul_mem (C.mul_mem hc hx.2) (C.inv_mem hc)⟩
    have h2 : n * (c * x * c⁻¹) * n⁻¹ = c * x * c⁻¹ := by
      rw [hab n hn _ h1.1, mul_inv_cancel_right]
    have e : n * c * x * (n * c)⁻¹ = n * (c * x * c⁻¹) * n⁻¹ := by group
    rw [e, h2]
    exact h1
  have hbot : N ⊓ C = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← hcore]
    exact Subgroup.normal_le_normalCore.mpr inf_le_right
  have hcompl : N.IsComplement' C :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hbot) hmul
  exact hcompl.index_eq_card

theorem solvable_normal_le_of_coatom {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hC : IsCoatom C) (hnp : ¬ IsPrimePow C.index) {R : Subgroup G} [R.Normal]
    (hR : Group.IsSolvable ↥R) : R ≤ C := by
  classical
  by_contra hRC
  set K := C.normalCore with hK
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hKC : K ≤ C := C.normalCore_le
  set Cb : Subgroup (G ⧸ K) := C.map π with hCb
  have hcomap : Cb.comap π = C := by
    rw [hCb, Subgroup.comap_map_eq, hker]
    exact sup_eq_left.mpr hKC
  have hCbc : IsCoatom Cb := by
    refine ⟨fun h => hC.1 ?_, fun D hD => ?_⟩
    · have h1 : (Cb.comap π) = (⊤ : Subgroup (G ⧸ K)).comap π := by rw [h]
      rw [hcomap, Subgroup.comap_top] at h1
      exact h1
    · have h1 : C < D.comap π := by
        have := (Subgroup.comap_lt_comap_of_surjective hπs).mpr hD
        rwa [hcomap] at this
      have h2 : D.comap π = ⊤ := hC.2 _ h1
      have h3 : D = (D.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs D).symm
      rw [h3, h2, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hπs]
  have hcoreb : Cb.normalCore = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := hπs x
    have hN : (Cb.normalCore.comap π).Normal := Cb.normalCore_normal.comap π
    have h1 : Cb.normalCore.comap π ≤ C := by
      intro z hz
      have : π z ∈ Cb := Subgroup.normalCore_le Cb hz
      rw [← hcomap]
      exact this
    have h2 : Cb.normalCore.comap π ≤ K := Subgroup.normal_le_normalCore.mpr h1
    have h3 : y ∈ K := h2 hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff y).mpr h3
  set Rb : Subgroup (G ⧸ K) := R.map π with hRb
  have hRbn : Rb.Normal := ‹R.Normal›.map π hπs
  have hRbne : Rb ≠ ⊥ := by
    intro h
    apply hRC
    intro r hr
    have : π r ∈ Rb := Subgroup.mem_map_of_mem π hr
    rw [h, Subgroup.mem_bot] at this
    exact hKC ((QuotientGroup.eq_one_iff r).mp this)
  have hRbs : Group.IsSolvable ↥Rb := by
    have := hR
    refine Group.isSolvable_of_surjective
      (f := (π.comp R.subtype).codRestrict Rb fun r => Subgroup.mem_map_of_mem π r.2) ?_
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨N, hNle, hNmin⟩ : ∃ N ≤ Rb, MinimalNontrivialNormal N :=
    Finite.exists_le_minimal (p := fun D : Subgroup (G ⧸ K) => D.Normal ∧ D ≠ ⊥) ⟨hRbn, hRbne⟩
  have hNn : N.Normal := hNmin.1.1
  have hNne : N ≠ ⊥ := hNmin.1.2
  have hNs : Group.IsSolvable ↥N := by
    have := hRbs
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNle)
  obtain ⟨r, hr, hel, d, hd, hcard⟩ := minimal_normal_solvable_elementary N hNmin hNs
  have hNC : ¬ N ≤ Cb := by
    intro h
    apply hNne
    rw [eq_bot_iff, ← hcoreb]
    exact Subgroup.normal_le_normalCore.mpr h
  have hidx := index_eq_card_of_abelian_normal hCbc hcoreb hNC fun a ha b hb => by
    have := hel.1
    exact setLike_mul_comm ha hb
  have hidx' : Cb.index = C.index := by
    rw [hCb]
    have h1 : (C.map π).index = C.index := by
      have := Subgroup.index_comap_of_surjective (f := π) hπs (H := Cb)
      rw [hcomap] at this
      exact this.symm
    exact h1
  apply hnp
  rw [← hidx', hidx, hcard]
  exact (isPrimePow_nat_iff _).2 ⟨r, d, hr, hd, rfl⟩

theorem four_dvd_ncard_of_orbits {G Ω : Type*} [Group G] [MulAction G Ω] (E : Subgroup G)
    (hE : IsPGroup 2 ↥E) (x₀ : Ω)
    (h4 : ∀ x : Ω, x ≠ x₀ → 4 ≤ {w : Ω | ∃ e ∈ E, e • x = w}.ncard) :
    ∀ n : ℕ, ∀ S : Set Ω, S.ncard = n → S.Finite → x₀ ∉ S → (∀ e ∈ E, ∀ s ∈ S, e • s ∈ S) →
      4 ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hfin hx₀ hinv
    by_cases hS : S = ∅
    · subst hS
      simp at hn
      omega
    · obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 hS
      set O : Set Ω := {w : Ω | ∃ e ∈ E, e • s = w} with hOdef
      have hOS : O ⊆ S := by
        rintro _ ⟨e, he, rfl⟩
        exact hinv e he s hs
      have hO : O = MulAction.orbit ↥E s := by
        ext w
        constructor
        · rintro ⟨e, he, rfl⟩
          exact ⟨⟨e, he⟩, rfl⟩
        · rintro ⟨e, rfl⟩
          exact ⟨e, e.2, rfl⟩
      have hOfin : O.Finite := hfin.subset hOS
      have hsx : s ≠ x₀ := fun h => hx₀ (h ▸ hs)
      have h4s : 4 ≤ O.ncard := h4 s hsx
      have hcardO : 4 ∣ O.ncard := by
        have : Finite ↥(MulAction.orbit ↥E s) := by
          rw [← hO]
          exact hOfin
        obtain ⟨k, hk⟩ := hE.card_orbit s
        have h1 : O.ncard = 2 ^ k := by
          rw [← hk, ← Nat.card_coe_set_eq, hO]
        rw [h1] at h4s ⊢
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have : k ≤ 1 := by omega
          have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
          omega
        exact ⟨2 ^ (k - 2), by
          rw [show 2 ^ k = 2 ^ 2 * 2 ^ (k - 2) by rw [← pow_add]; congr 1; omega]
          norm_num⟩
      have hrest : (S \ O).ncard = n - O.ncard := by
        rw [Set.ncard_sdiff hOS hOfin, hn]
      have hOle : O.ncard ≤ n := hn ▸ Set.ncard_le_ncard hOS hfin
      have hOpos : 0 < O.ncard := by omega
      have hlt : n - O.ncard < n := by omega
      have hrestinv : ∀ e ∈ E, ∀ w ∈ S \ O, e • w ∈ S \ O := by
        rintro e he w ⟨hwS, hwO⟩
        refine ⟨hinv e he w hwS, fun ⟨e', he', hew⟩ =>
          hwO ⟨e⁻¹ * e', E.mul_mem (E.inv_mem he) he', ?_⟩⟩
        rw [mul_smul, hew, inv_smul_smul]
      have h1 := ih (n - O.ncard) hlt (S \ O) hrest (hfin.sdiff) (fun h => hx₀ h.1) hrestinv
      have : n = O.ncard + (n - O.ncard) := by omega
      rw [this]
      exact Nat.dvd_add hcardO h1

theorem ncard_mod_four_eq_one {G Ω : Type*} [Group G] [MulAction G Ω] (E : Subgroup G)
    (hE : IsPGroup 2 ↥E) (x₀ : Ω) (hfix : ∀ e ∈ E, e • x₀ = x₀)
    (h4 : ∀ x : Ω, x ≠ x₀ → 4 ≤ {w : Ω | ∃ e ∈ E, e • x = w}.ncard)
    (S : Set Ω) (hfin : S.Finite) (hinv : ∀ e ∈ E, ∀ s ∈ S, e • s ∈ S) (hx₀ : x₀ ∈ S) :
    S.ncard % 4 = 1 := by
  have h1 : (S \ {x₀}).ncard + 1 = S.ncard := by
    have := Set.ncard_sdiff_singleton_add_one hx₀ hfin
    exact this
  have h2 : 4 ∣ (S \ {x₀}).ncard := by
    refine four_dvd_ncard_of_orbits E hE x₀ h4 _ (S \ {x₀}) rfl hfin.sdiff (fun h => h.2 rfl) ?_
    rintro e he s ⟨hsS, hs0⟩
    refine ⟨hinv e he s hsS, fun h => hs0 ?_⟩
    have : s = e⁻¹ • (e • s) := (inv_smul_smul e s).symm
    rw [this]
    have h' : e • s = x₀ := h
    rw [h']
    exact (inv_smul_eq_iff.mpr (hfix e he).symm)
  omega

theorem solvable_normal_le_of_maximal {J : Type*} [Group J] [Finite J] {G C R : Subgroup J}
    (hCG : C ≤ G) (hCne : C ≠ G) (hmax : ∀ D : Subgroup J, C ≤ D → D ≤ G → D = C ∨ D = G)
    (hnp : ¬ IsPrimePow (C.relIndex G)) (hRG : R ≤ G)
    (hN : G ≤ Subgroup.normalizer (R : Set J)) (hR : Group.IsSolvable ↥R) : R ≤ C := by
  have hcoatom : IsCoatom (C.subgroupOf G) := by
    refine ⟨fun h => hCne ?_, fun D' hD' => ?_⟩
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact le_antisymm hCG h
    · set D : Subgroup J := D'.map G.subtype with hD
      have hDG : D ≤ G := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hCD : C ≤ D := by
        intro c hc
        exact ⟨⟨c, hCG hc⟩, hD'.le (Subgroup.mem_subgroupOf.mpr hc), rfl⟩
      rcases hmax D hCD hDG with h | h
      · exfalso
        apply hD'.not_ge
        intro x hx
        have : (x : J) ∈ D := ⟨x, hx, rfl⟩
        rw [h] at this
        exact Subgroup.mem_subgroupOf.mpr this
      · refine eq_top_iff.mpr fun x _ => ?_
        have : (x : J) ∈ D := by rw [h]; exact x.2
        obtain ⟨y, hy, hyx⟩ := this
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
  have hnorm : (R.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hN g.2) (x : J)).mp hx
    simpa using this
  have hsolv : Group.IsSolvable ↥(R.subgroupOf G) := by
    have := hR
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hRG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRG).symm.surjective
  have h := solvable_normal_le_of_coatom hcoatom hnp hsolv
  intro r hr
  exact Subgroup.mem_subgroupOf.mp
    (h (Subgroup.mem_subgroupOf.mpr hr : (⟨r, hRG hr⟩ : ↥G) ∈ R.subgroupOf G))

end CFSG.Quasithin.J4Rad
