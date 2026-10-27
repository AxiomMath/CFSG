module

public import CFSG.Quasithin.H13.A5Z1367b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section Factor

variable {V : Type} [CommGroup V] [Finite V]

theorem center_eq_bot_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (Subgroup.center X) inferInstance with
    h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp this a)

theorem centralizer_eq_bot_of_simple {G N : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥G)
    (hN : IsComponentOf N G) : N = G ∧ G ⊓ Subgroup.centralizer (N : Set (MulAut V)) = ⊥ := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  have hnc : ∃ a b : ↥G, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply not_le_centralizer_self_of_qs hq
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hN.1 hy⟩ ⟨x, hN.1 hx⟩)
  have hNG : N = G := by
    have hqG : CFSG.IsQuasisimple ↥G := by
      refine ⟨?_, ?_, ?_⟩
      · rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (commutator ↥G) inferInstance
          with h | h
        · exfalso
          obtain ⟨a, b, hab⟩ := hnc
          have h1 : ⁅a, b⁆ ∈ commutator ↥G :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
          have h2 : ⁅a, b⁆ ∈ (⊥ : Subgroup ↥G) := h ▸ h1
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
          exact hab h2
        · exact ⟨h⟩
      · exact @MulEquiv.isSimpleGroup _ _ _ _ hs ((QuotientGroup.quotientMulEquivOfEq
          (center_eq_bot_of_simple hs hnc)).trans QuotientGroup.quotientBot)
      · obtain ⟨a, b, hab⟩ := hnc
        refine ⟨a, b, fun h => hab ?_⟩
        have hZ := center_eq_bot_of_simple hs ⟨a, b, hab⟩
        have h' : ((a * b : ↥G) : ↥G ⧸ Subgroup.center ↥G) =
            ((b * a : ↥G) : ↥G ⧸ Subgroup.center ↥G) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
          exact h
        rw [QuotientGroup.eq, hZ, Subgroup.mem_bot] at h'
        exact inv_mul_eq_one.mp h'
    exact eq_of_subnormal_qs hN.2.1 hq hqG
  refine ⟨hNG, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hZ := center_eq_bot_of_simple hs hnc
  have hxZ : (⟨x, hx.1⟩ : ↥G) ∈ Subgroup.center ↥G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := Subgroup.mem_centralizer_iff.mp hx.2 (y : MulAut V) (hNG ▸ y.2)
    exact Subtype.ext h
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)

theorem centralizer_alt_five_eq_bot :
    Subgroup.centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))) = ⊥ := by
  by_contra hne
  have hn : (Subgroup.centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5)))).Normal :=
    Subgroup.normal_centralizer
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (by simp)
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hne)
  have hcomm : ∀ a ∈ alternatingGroup (Fin 5), ∀ b ∈ alternatingGroup (Fin 5), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hA hb) a ha
  have hc : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap 1 2 * Equiv.swap 2 3) ≠
      (Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) := by
    decide
  exact hc (hcomm _ (by decide) _ (by decide))

theorem centralizer_eq_bot_of_perm_five {G N : Subgroup (MulAut V)} (e : ↥G ≃* Equiv.Perm (Fin 5))
    (hN : IsComponentOf N G) :
    G ⊓ Subgroup.centralizer (N : Set (MulAut V)) = ⊥ ∧ Nat.card ↥N = 60 := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  obtain ⟨hp, -⟩ := qs_perfect_ne_bot hq
  set N' : Subgroup ↥G := N.subgroupOf G with hN'
  set M : Subgroup (Equiv.Perm (Fin 5)) := N'.map e.toMonoidHom with hM
  have eN : ↥N ≃* ↥M := (Subgroup.subgroupOfEquivOfLe hN.1).symm.trans
    (N'.equivMapOfInjective e.toMonoidHom e.injective)
  have hqM : CFSG.IsQuasisimple ↥M := CFSG.LocalCores.isQuasisimple_of_mulEquiv eN hq
  have hsubM : IsSubnormal M ⊤ := by
    have h1 := A3.subnormal_comap G.subtype hN.2.1
    rw [show G.comap G.subtype = ⊤ from Subgroup.subgroupOf_self G] at h1
    have h2 := A3.subnormal_map e.toMonoidHom h1
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have hMp : ⁅M, M⁆ = M := S153L.comp_perfect_of_isQuasisimple hqM
  have hMA : M ≤ alternatingGroup (Fin 5) := by
    rw [← hMp, ← alternatingGroup.commutator_perm_eq (by simp), commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hA5s : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hcardA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hqA : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    S153L.comp_quasisimple_of_simple hA5s (by rw [hcardA]; norm_num)
  have hMeq : M = alternatingGroup (Fin 5) :=
    eq_of_subnormal_qs (A3.subnormal_of_le_of_le hsubM hMA le_top) hqM hqA
  refine ⟨?_, by rw [Nat.card_congr eN.toEquiv, hMeq, hcardA]⟩
  rw [eq_bot_iff]
  intro x hx
  have hx1 : e ⟨x, hx.1⟩ ∈ Subgroup.centralizer
      (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))) := by
    rw [← hMeq, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hx.2 (n : MulAut V) (Subgroup.mem_subgroupOf.mp hn)
    show e n * e ⟨x, hx.1⟩ = e ⟨x, hx.1⟩ * e n
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  rw [centralizer_alt_five_eq_bot, Subgroup.mem_bot] at hx1
  have : (⟨x, hx.1⟩ : ↥G) = 1 := e.injective (by rw [hx1, map_one])
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem three_dvd_card_statedSL_three {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) : 3 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
  rw [card_statedSL_three1527d, hF]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul, mul_comm, pow_mul]
  have h := Nat.sub_dvd_pow_sub_pow 4 1 m
  simpa using h

theorem factor_kind {G N : Subgroup (MulAut V)} (hf : B56FactorList ↥G)
    (hN : IsComponentOf N G) :
    G ⊓ Subgroup.centralizer (N : Set (MulAut V)) = ⊥ ∧
    ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 2 ≤ n ∧ Nat.card F = 2 ^ n ∧
        Nonempty (↥G ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))) ∨
      (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ 3 ∣ Nat.card ↥N) ∨
      (∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Odd m ∧ Nat.card F = 2 ^ m ∧
        Nonempty (↥G ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧ 3 ∣ Nat.card ↥N)) := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  rcases hf with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, hm1, hm, hF, ⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · exfalso
      have hn1 : n = 1 := by omega
      subst hn1
      have h6 : Nat.card ↥G = 6 := by
        rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
        norm_num
      exact not_qs_of_le_solvable hN.1 (S153L.comp_solvable_of_card_six h6) hq
    · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hs : IsSimpleGroup ↥G :=
        @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) e
      exact ⟨(centralizer_eq_bot_of_simple hs hN).2, Or.inl ⟨n, F, inferInstance, inferInstance,
        hn2, hF, ⟨e⟩⟩⟩
  · obtain ⟨h1, h60⟩ := centralizer_eq_bot_of_perm_five e hN
    exact ⟨h1, Or.inr (Or.inl ⟨⟨e⟩, by rw [h60]; norm_num⟩)⟩
  · have hs : IsSimpleGroup ↥G :=
      @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_three_odd hF hm) e
    obtain ⟨hNG, hC⟩ := centralizer_eq_bot_of_simple hs hN
    refine ⟨hC, Or.inr (Or.inr ⟨m, F, inferInstance, inferInstance, hm, hF, ⟨e⟩, ?_⟩)⟩
    rw [hNG, Nat.card_congr e.toEquiv]
    exact three_dvd_card_statedSL_three hF

end Factor

end CFSG.Quasithin.H13.A5
