module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Borel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M

namespace E217R3

variable {G : Type} [Group G] [Finite G]

theorem false_of_oddPairedBorel
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    {H T M V K : Subgroup G} (h : Hyp2 H T M V) (hns : ¬ Group.IsSolvable H)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (h1 : Case1 H T M K) {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', hDker⟩ :=
    qrcHyp_of_hyp28 h.hyp h.charTwo
  have := hel
  obtain ⟨-, -, -, hKn, hCK, -, -, -, -, -⟩ :=
    H13.QRC.bender_section_setup hns T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ := exists_paired_of_case1_aux h38 h.hyp hKc hHK h1
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set K₁ := barIn M H K with hK₁
  set S := (T' : Subgroup H).map π with hSdef
  rw [hK] at hKn hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  set K₂ := K₁.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  obtain ⟨v₀, hv02, hv01, -, hv0M, -⟩ := exists_vbar h
  set e := starEquiv hMH with he
  set v : ↥H ⧸ D := e.symm v₀ with hv
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul, hv02, map_one]
  have hv1 : v ≠ 1 := fun h' => hv01 (by
    have := congrArg e h'
    rw [hv, MulEquiv.apply_symm_apply, map_one] at this
    exact this)
  have hvc : ∀ y : ↥H ⧸ D, e y ∈ E2.star M H M → y * v = v * y := by
    intro y hy
    apply e.injective
    rw [map_mul, map_mul, hv, MulEquiv.apply_symm_apply]
    exact hv0M (e y) hy
  have hSstar : S.map e.toMonoidHom = E2.star M H T := by
    have hST : S = barIn M H T := by rw [hSdef, hT']; rfl
    rw [hST]
    exact map_barIn_starEquiv hMH T
  have hStarTM : E2.star M H T ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hmp.le)
  have htS : π t₀ ∈ S := ⟨t₀, hT' ▸ ht₀T, rfl⟩
  have hvt : π t₀ * v = v * π t₀ :=
    hvc _ (hStarTM (hSstar ▸ Subgroup.mem_map_of_mem _ htS))
  have hBend : E2.IsBenderOf n ↥(E2.star M H K) := ⟨hn, by
    rcases hL with h' | h'
    exacts [Or.inl h', Or.inr (Or.inl h')]⟩
  have hsimp : IsSimpleGroup ↥K₁ :=
    haveI := isSimpleGroup_of_isBenderOf hBend
    φ.isSimpleGroup
  have hrig : BorelRigid ↥K₁ := BorelRigid.of_mulEquiv φ (borelRigid_of_family (Or.inl hBend))
  have hK₁e : (E2.star M H K).map e.symm.toMonoidHom = K₁ := by
    rw [← map_barIn_starEquiv hMH K, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  obtain ⟨S₁, hS₁, hB₁⟩ := isBorelIn_map e.symm hB
  rw [hK₁e] at hS₁ hB₁
  have hB₁M : ∀ b ∈ (E2.star M H (M ⊓ K)).map e.symm.toMonoidHom, b * v = v * b := by
    rintro _ ⟨x, hx, rfl⟩
    have hxM : e (e.symm x) ∈ E2.star M H M := by
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left) hx
    exact hvc _ hxM
  have hBne : (E2.star M H (M ⊓ K)).map e.symm.toMonoidHom ≠ ⊥ := by
    intro hbot
    rw [hB₁, Subgroup.eq_bot_iff_forall] at hbot
    have hS1 : S₁ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact hbot x ⟨hS₁.1 hx, Subgroup.le_normalizer hx⟩
    have htop : Subgroup.normalizer ((⊥ : Subgroup (↥H ⧸ D)) : Set (↥H ⧸ D)) = ⊤ := by
      rw [Subgroup.normalizer_eq_top_iff]
      infer_instance
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥K₁)
    refine ha (Subtype.ext (hbot a ⟨a.2, ?_⟩))
    rw [hS1, htop]
    exact Subgroup.mem_top _
  have hvN : v ∈ Subgroup.normalizer (K₁ : Set (↥H ⧸ D)) :=
    mem_normalizer_of_paired hKn hc hsimp (hB₁ ▸ inf_le_left) hBne fun b hb => (hB₁M b hb).symm
  have hv₁ : ∀ k ∈ K₁, v * k = k * v :=
    centralizes_of_borelRigid hrig hS₁ hv2 hvN fun b hb => (hB₁M b (hB₁ ▸ hb)).symm
  have hv₂ : ∀ k ∈ K₂, v * k = k * v := commute_of_mem_map_conj hvt.symm hv₁
  refine hv1 (hCK v fun k hk => ?_)
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({v} : Set (↥H ⧸ D)) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hv₁ k hk).symm)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hv₂ k hk).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hk)).symm

theorem r3Pkg1a
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) :
    R3Pkg1a := by
  intro G _ _ H T M V K hS hlt h1 n hn hL hB
  exact false_of_oddPairedBorel h38 hS.toHyp2 hS.not_solvable hS.mem_cComp hS.eq_sup h1 hn hL hB

end E217R3

end CFSG.Quasithin
