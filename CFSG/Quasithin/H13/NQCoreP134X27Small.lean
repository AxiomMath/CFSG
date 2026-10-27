module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.F134A7Config
public import CFSG.Quasithin.Vol2.F134L2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieIso

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Ch1

theorem E9Cfg.false_of_normal_three {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (h : E9Cfg L P T) (hcard : Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 72)
    (N : Subgroup A) (hNH : N ≤ P ⊔ (T ⊓ L)) (hN3 : Nat.card N = 3)
    (hNnorm : ∀ x ∈ P ⊔ (T ⊓ L), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hP : ∃ x ∈ P ⊔ (T ⊓ L), ∃ p ∈ P, x * p * x⁻¹ ∉ P) : False := by
  set H := P ⊔ (T ⊓ L) with hHdef
  have hPH : P ≤ H := le_sup_left
  have hNP : N ≤ P := F134.le_of_card_three hcard hPH h.card hNH hN3 hNnorm
  have hL := h.normal
  have htH : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ H, t * x * t⁻¹ ∈ H := by
    intro t ht
    refine F134.conj_mem_sup (fun p hp => Subgroup.mem_sup_left ?_)
      (fun s hs => Subgroup.mem_sup_right ?_)
    · exact (Subgroup.mem_normalizer_iff.mp ht.2 p).1 hp
    · exact ⟨T.mul_mem (T.mul_mem ht.1 hs.1) (T.inv_mem ht.1), hL.conj_mem s hs.2 t⟩
  have hinv : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t⁻¹ ∈ T ⊓ Subgroup.normalizer (P : Set A) :=
    fun t ht => (T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht
  have hnormN : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (N : Set A) := by
    intro t ht
    set Nt := N.map (MulAut.conj t).toMonoidHom
    have hNt3 : Nat.card Nt = 3 := by
      rw [← hN3]
      exact (Nat.card_congr (N.equivMapOfInjective _ (MulAut.conj t).injective).toEquiv).symm
    have hNtH : Nt ≤ H := by
      rintro _ ⟨n, hn, rfl⟩
      exact htH t ht n (hNH hn)
    have hNtnorm : ∀ x ∈ H, ∀ n ∈ Nt, x * n * x⁻¹ ∈ Nt := by
      rintro x hx _ ⟨n, hn, rfl⟩
      have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ H := htH t⁻¹ (hinv t ht) x hx
      refine ⟨t⁻¹ * x * t⁻¹⁻¹ * n * (t⁻¹ * x * t⁻¹⁻¹)⁻¹, hNnorm _ hx' n hn, ?_⟩
      change t * (t⁻¹ * x * t⁻¹⁻¹ * n * (t⁻¹ * x * t⁻¹⁻¹)⁻¹) * t⁻¹ = x * (t * n * t⁻¹) * x⁻¹
      group
    have hNtP : Nt ≤ P := F134.le_of_card_three hcard hPH h.card hNtH hNt3 hNtnorm
    have hNt : Nt = N := by
      by_contra hne
      have hsup := F134.sup_eq_of_card_three h.card hNP hNtP hN3 hNt3 (Ne.symm hne)
      obtain ⟨x, hx, p, hp, hxp⟩ := hP
      refine hxp ?_
      rw [← hsup] at hp ⊢
      exact F134.conj_mem_sup (fun n hn => Subgroup.mem_sup_left (hNnorm x hx n hn))
        (fun n hn => Subgroup.mem_sup_right (hNtnorm x hx n hn)) p hp
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [← hNt]
      exact ⟨n, hn, rfl⟩
    · intro hn
      rw [← hNt] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      have : m = n := by
        have hmn' : t * m * t⁻¹ = t * n * t⁻¹ := hmn
        simpa using hmn'
      rwa [← this]
  rcases h.irred N hNP hnormN with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hN3
    omega
  · rw [htop, h.card] at hN3
    omega

theorem noE9Cfg_alt7 :
    NoE9Cfg fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 7)) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := P ⊔ (T ⊓ L) with hHdef
  have hHL : H ≤ L := E9Cfg.sup_inf_le hcfg
  have hPH : P ≤ H := le_sup_left
  have hS := E9Cfg.isSylowTwoOf_inf hcfg
  have hL : Nat.card L = 2520 := (Nat.card_congr e.toEquiv).trans F134.card_alternating_seven
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hidx := ((T ⊓ L).subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hk, hL] at hidx
  have hk3 : k = 3 := by
    have hodd := hS.2.2
    have hle : k ≤ 3 := by
      by_contra hlt
      have : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ hidx)
      norm_num at this
    interval_cases k <;> omega
  have hcard : Nat.card H = 72 := by
    rw [E9Cfg.card_sup_inf hcfg, hk, hk3]
    norm_num
  have hP' : Nat.card ((P.subgroupOf L).map e.toMonoidHom) = 9 := by
    rw [← Nat.card_congr ((P.subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  obtain ⟨hP'p, hP'i⟩ := F134.isSylow_three_of_card_nine hP'
  obtain ⟨hP₀p, hP₀i⟩ := F134.isSylow_three_of_card_nine F134.card_a7P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hP'p.toSylow hP'i)
    (hP₀p.toSylow hP₀i)
  let ψ : ↥L ≃* alternatingGroup (Fin 7) := e.trans (MulAut.conj g)
  have hψP : (P.subgroupOf L).map ψ.toMonoidHom = F134.a7P₀ := by
    have hg' := congrArg (fun Q : Sylow 3 (alternatingGroup (Fin 7)) =>
      (Q : Subgroup (alternatingGroup (Fin 7)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow, Subgroup.pointwise_smul_def] at hg'
    have key : ((P.subgroupOf L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (P.subgroupOf L).map ψ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [← key]
    exact hg'
  set H'' := (H.subgroupOf L).map ψ.toMonoidHom with hH''def
  have hH'' : Nat.card H'' = 72 := by
    rw [← Nat.card_congr ((H.subgroupOf L).equivMapOfInjective _ ψ.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv, hcard]
  have hP₀H : F134.a7P₀ ≤ H'' := by
    rw [← hψP]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hPH)
  obtain ⟨⟨N'', hN''H, hN''3, hN''norm⟩, x'', hx'', p'', hp'', hnot⟩ :=
    F134.a7_key H'' (hP₀H (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
      (hP₀H (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) hH''
  refine E9Cfg.false_of_normal_three hcfg hcard ((N''.comap ψ.toMonoidHom).map L.subtype) ?_ ?_
    ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (F134.mem_map_subgroupOf_iff ψ m).1 (hN''H hm)
  · rw [← Nat.card_congr ((N''.comap ψ.toMonoidHom).equivMapOfInjective _
      L.subtype_injective).toEquiv, ← hN''3,
      Nat.card_congr ((N''.comap ψ.toMonoidHom).equivMapOfInjective ψ.toMonoidHom
        ψ.injective).toEquiv,
      Subgroup.map_comap_eq_self_of_surjective ψ.surjective]
  · rintro x hx _ ⟨m, hm, rfl⟩
    set x' : ↥L := ⟨x, hHL hx⟩
    have hx' : ψ x' ∈ H'' := (F134.mem_map_subgroupOf_iff ψ x').2 hx
    refine ⟨x' * m * x'⁻¹, ?_, rfl⟩
    show ψ (x' * m * x'⁻¹) ∈ N''
    rw [map_mul, map_mul, map_inv]
    exact hN''norm _ hx' _ hm
  · obtain ⟨x', hx'⟩ : ∃ x' : ↥L, ψ x' = x'' := ⟨ψ.symm x'', ψ.apply_symm_apply x''⟩
    obtain ⟨p', hp'⟩ : ∃ p' : ↥L, ψ p' = p'' := ⟨ψ.symm p'', ψ.apply_symm_apply p''⟩
    have hxH : (x' : A) ∈ H := (F134.mem_map_subgroupOf_iff ψ x').1 (hx' ▸ hx'')
    have hpP : (p' : A) ∈ P := (F134.mem_map_subgroupOf_iff ψ p').1 (hψP ▸ hp' ▸ hp'')
    refine ⟨x', hxH, p', hpP, fun hmem => hnot ?_⟩
    rw [← hψP, ← hx', ← hp', ← map_inv, ← map_mul, ← map_mul]
    exact (F134.mem_map_subgroupOf_iff ψ (x' * p' * x'⁻¹)).2 hmem

theorem not_dvd_card_alt {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    ¬ 27 ∣ Nat.card (alternatingGroup (Fin n)) := by
  interval_cases n <;> rw [nat_card_alternatingGroup] <;>
    simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem noX27Simple_alt {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    NoX27Simple fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin n)) :=
  noX27Simple_of_not_dvd fun _ _ ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_alt h5 h8

theorem facts134X27_alt
    (hA6 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 6))) :
    ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin n)) := by
  intro n h5 h8
  interval_cases n
  · refine noX27ConfigQ_of_noCover (isoInvariant_alt 5) (noX27Simple_alt le_rfl (by norm_num)) ?_
    intro X _ _ hX h3 ⟨e⟩
    have : Group.IsPerfect X := hX.1
    exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      (CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num) (by norm_num) π hπ hC
        hodd).1 (Or.inl rfl)
  · exact hA6
  · exact noX27ConfigQ_of_noE9Cfg (isoInvariant_alt 7) (noX27Simple_alt (by norm_num) (by norm_num))
      noE9Cfg_alt7
  · refine noX27ConfigQ_of_noCover (isoInvariant_alt 8) (noX27Simple_alt (by norm_num) le_rfl) ?_
    intro X _ _ hX h3 ⟨e⟩
    have : Group.IsPerfect X := hX.1
    exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      (CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num) (by norm_num) π hπ hC
        hodd).1 (Or.inr rfl)

theorem facts134X27_psl2Odd
    (hA6 : NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 6))) :
    ∀ r f : ℕ, r.Prime → r ≠ 2 → (f = 1 ∨ f = 2) →
      NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 r f := by
  intro r f hr hr2 hf
  by_cases hr3 : r = 3
  · subst hr3
    rcases hf with rfl | rfl
    · intro A _ _ L P T _ _ _ h
      exact absurd (by norm_num : ((2 : ℕ), 3 ^ 1) = (2, 3)) h.1.2.2.2.2
    · intro A _ _ L P T hcfg h27 hZ h
      exact hA6 A L P T hcfg h27 hZ (alternating_six_of_psl_two_nine h)
  · have hr5 : 3 < r := by
      have := hr.two_le
      omega
    refine noX27ConfigQ_of_noCover (isoInvariant_stated _ _ _ _)
      (noX27Simple_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSL_two hr3 h) ?_
    intro X _ _ hX h3 h
    exact false_of_a134TypesCentral hX h3
      (Or.inr (Or.inr (Or.inr ⟨r, f, hr, hr5, by omega, by omega, h⟩)))

theorem facts134X27_psl2Even :
    ∀ f : ℕ, 2 ≤ f →
      NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 f := fun f _ =>
  noX27ConfigQ_of_noCover (isoInvariant_stated _ _ _ _)
    (noX27Simple_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSL_two (by norm_num) h)
    fun _ _ _ hX h3 h => false_of_a134TypesCentral hX h3 (Or.inl ⟨f, h⟩)

theorem facts134X27_sz :
    ∀ f : ℕ, Odd f → 3 ≤ f →
      NoX27ConfigQ fun (X : Type) [Group X] => SuzukiModel X 2 f := fun f _ _ =>
  noX27ConfigQ_of_noCover (fun _ _ _ _ e h => CFSG.SectionRank.suzukiModel_of_mulEquiv e.symm h)
    (noX27Simple_of_not_dvd fun _ _ h hd =>
      F134.not_three_dvd_card_of_suzukiModel h (dvd_trans (by norm_num) hd))
    fun _ _ _ hX h3 h => false_of_a134TypesCentral hX h3 (Or.inr (Or.inl ⟨f, h⟩))

theorem facts134X27_psl45 :
    ∀ n : ℕ, (n = 4 ∨ n = 5) →
      NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1 := by
  intro n hn
  refine noX27ConfigQ_of_noCover (isoInvariant_stated _ _ _ _)
    (noX27Simple_of_not_dvd fun _ _ h => ?_) fun _ _ _ hX h3 h =>
      false_of_linear_four_five hX h3 hn h
  rcases hn with rfl | rfl
  · rw [CFSG.Quasithin.F420.card_of_l42 h]
    norm_num
  · rw [CFSG.Quasithin.F420.card_of_l52 h]
    norm_num

end CFSG.Quasithin.H13.NQCore
