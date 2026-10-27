module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425F
public import CFSG.Quasithin.Vol2.Ch4Sec2T425E

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_prime_dvd_of_quasisimple {L : Subgroup G}
    (hL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card L := by
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  suffices h : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card Q by
    obtain ⟨r, hr, hr2, hrQ⟩ := h
    exact ⟨r, hr, hr2, hrQ.trans (Subgroup.card_quotient_dvd_card _)⟩
  by_contra hcon
  push Not at hcon
  have hpos : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card Q = 2 ^ (Nat.card Q).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdvd => by
      by_contra hne
      exact hcon d hd hne hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 Q := IsPGroup.of_card hpow
  have hnil : Group.IsNilpotent Q := hP.isNilpotent
  have hsolv : Group.IsSolvable Q := inferInstance
  have hnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hL.2.2
    have : Subsingleton (Q ⧸ Subgroup.center Q) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center Q))
    exact hab (Subsingleton.elim _ _)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (Group.isPerfect_def.mp hL.1)

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem lemma_4_2_10 (c : Inp425 G) {K : Subgroup G} (hK : K ∈ cComp M) (hKH : ¬ K ≤ H)
    {h : G} (hh : h ∈ H) (hhM : h ∉ M) :
    L.map (MulAut.conj h).toMonoidHom ≤ K ∧ M ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card L → CFSG.Open.pRank p K ≤ 1 := by
  classical
  set C := centralizerSection M L (pCoreOf 2 L) with hCdef
  set J := L.map (MulAut.conj h).toMonoidHom with hJdef
  have hC2 := s.pCoreOf_C_ne_bot c
  have hKC := s.K_le_C c hK hKH
  have hJC := s.J_le_C c hh hhM
  have hCM : C ≤ M := centralizerSection_le_left _ _ _
  have hKcC : K ∈ cComp C := cComp_mem_of_le hK hKC hCM
  obtain ⟨p, hp, hp2, hpL⟩ := exists_odd_prime_dvd_of_quasisimple s.hyp.quasisimple
  have : Fact p.Prime := ⟨hp⟩
  have hrank := s.pRank_C_le_one hp2 hpL
  have huniq : ∀ A ∈ cComp C, ∀ B ∈ cComp C, p ∣ Nat.card A → p ∣ Nat.card B → A = B :=
    fun A hA B hB hpA hpB => T425.eq_of_dvd_of_pRank_le_one s.hyp.qtke s.hyp.simple
      s.hyp.nonabelian c.a37 hC2 hp2 hrank hA hB hpA hpB
  have hnorm : ∀ A ∈ cComp C, ∀ B ∈ cComp C, A ≤ Subgroup.normalizer (B : Set G) := by
    intro A hA B hB
    by_cases hAB : A = B
    · rw [hAB]
      exact Subgroup.le_normalizer
    · have h1 := (lemma_1_2_1_two s.hyp.qtke s.hyp.simple s.hyp.nonabelian c.a37 hC2 hA hB
        hAB).1
      exact Subgroup.le_normalizer_iff_commutator_le_right.mpr
        (h1.trans (inf_le_right.trans (pCoreOf_le 2 B)))
  set S : Finset (Subgroup G) := (Set.toFinite (cComp C)).toFinset with hS
  have hmemS : ∀ A, A ∈ S ↔ A ∈ cComp C := fun A => Set.Finite.mem_toFinset _
  set K₀ : Subgroup G := ⨆ A ∈ S, A with hK₀
  have hK₀eq : K₀ = perfectCore C := by
    rw [← lemma_1_2_1_one s.hyp.qtke s.hyp.simple s.hyp.nonabelian c.a39 hC2, hK₀, cCompSpan,
      sSup_eq_iSup]
    exact iSup_congr fun A => iSup_congr_Prop (hmemS A) fun _ => rfl
  have hJp : ⁅J, J⁆ = J := by rw [hJdef, ← Subgroup.map_commutator, s.hyp.perfect]
  have hJK₀ : J ≤ K₀ := hK₀eq ▸ le_perfectCore_of_perfect hJC hJp
  obtain ⟨x, hxL, hxo, -, l, hl, hxl⟩ := T425.exists_noncentral hp2 s.hyp.perfect hpL
    (X := ⊥) IsPGroup.of_bot bot_le fun y hy l _ => by
      rw [Subgroup.mem_bot.mp hy]
      simp
  set z := h * x * h⁻¹ with hz
  have hzJ : z ∈ J := ⟨x, hxL, by simp [hz, MulAut.conj_apply]⟩
  have hzo : orderOf z = p := by rw [hz, C2Eleven.orderOf_conj_eq]; exact hxo
  obtain ⟨Y, hY, hpY⟩ : ∃ Y ∈ cComp C, p ∣ Nat.card Y := by
    by_contra hno
    push Not at hno
    apply T425.not_dvd_card_iSup₂ hp S (fun A hA => hno A ((hmemS A).mp hA))
      (fun A hA B hB => hnorm A ((hmemS A).mp hA) B ((hmemS B).mp hB))
    have h1 := Subgroup.orderOf_dvd_natCard K₀ (hJK₀ hzJ)
    rwa [hzo] at h1
  set W : Subgroup G := ⨆ A ∈ S.erase Y, A with hW
  have hWp : ¬ p ∣ Nat.card W := T425.not_dvd_card_iSup₂ hp (S.erase Y)
    (fun A hA hpA => Finset.ne_of_mem_erase hA
      (huniq A ((hmemS A).mp (Finset.mem_of_mem_erase hA)) Y hY hpA hpY))
    (fun A hA B hB => hnorm A ((hmemS A).mp (Finset.mem_of_mem_erase hA)) B
      ((hmemS B).mp (Finset.mem_of_mem_erase hB)))
  have hWY : W ≤ Subgroup.normalizer (Y : Set G) :=
    iSup₂_le fun A hA => hnorm A ((hmemS A).mp (Finset.mem_of_mem_erase hA)) Y hY
  have hK₀WY : K₀ = Y ⊔ W := by
    rw [hK₀, ← Finset.insert_erase ((hmemS Y).mpr hY), Finset.iSup_insert]
  have hzY : z ∈ Y := T425.mem_of_pow_eq_one hp hWY hWp
    (by rw [sup_comm, ← hK₀WY]; exact hJK₀ hzJ) (k := 1)
    (by rw [pow_one, ← hzo]; exact pow_orderOf_eq_one z)
  have hJN : J ≤ Subgroup.normalizer (Y : Set G) :=
    hJK₀.trans (iSup₂_le fun A hA => hnorm A ((hmemS A).mp hA) Y hY)
  have hJY : J ≤ Y := by
    set Y' := Y.map (MulAut.conj h⁻¹).toMonoidHom with hY'
    have hLN : L ≤ Subgroup.normalizer (Y' : Set G) := by
      intro l' hl'
      have hn : h * l' * h⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
        have := hJN ⟨l', hl', rfl⟩
        simpa [MulAut.conj_apply] using this
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_map_conj_iff, mem_map_conj_iff, inv_inv]
      have e : h * (l' * y * l'⁻¹) * h⁻¹ =
          (h * l' * h⁻¹) * (h * y * h⁻¹) * (h * l' * h⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp hn _
    have hxY' : x ∈ Y' := by
      rw [mem_map_conj_iff, inv_inv]
      exact hzY
    have hLY' := T425.le_of_noncentral_mem s.hyp.perfect s.hyp.quasisimple hLN hxL hxY' hl hxl
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hLY' hy
    rw [mem_map_conj_iff, inv_inv] at h1
    simpa [MulAut.conj_apply] using h1
  have hKY : K = Y := by
    by_contra hne
    apply hKH
    have hKYc := (lemma_1_2_1_two s.hyp.qtke s.hyp.simple s.hyp.nonabelian c.a37 hC2 hKcC hY
      hne).1
    have hCsub : IsSubnormal C M :=
      A3.subnormal_of_normal hCM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr (s.le_normalizer_C c))
    have hYM : IsSubnormal Y M := A3.subnormal_trans (subnormal_of_mem_cComp hY) hCsub
    set P := pCoreOf 2 M with hPdef
    have hO2Y : pCoreOf 2 Y ≤ P := fun y hy => A4.pCoreOf_le_of_subnormal 2 hYM hy
    set H₀ := conjClosure L H with hH₀
    have hH₀eq : H₀ = L ⊔ J :=
      le_antisymm (s.H0_le_sup c hh hhM)
        (sup_le (le_conjClosure L H) (s.conj_h c hh hhM).2.2)
    have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
      hKC.trans fun x hx => (mem_centralizerSection.mp hx).2.1
    have hKN : K ≤ Subgroup.normalizer ((H₀ ⊔ P : Subgroup G) : Set G) := by
      intro k hk
      have hkM : k ∈ M := le_of_mem_cComp hK hk
      have hkL : L.map (MulAut.conj k).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKL hk)
      have hkP : P.map (MulAut.conj k).toMonoidHom = P :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_pCoreOf 2 M hkM)
      have hkJ : J.map (MulAut.conj k).toMonoidHom ≤ J ⊔ P := by
        rintro _ ⟨j, hj, rfl⟩
        have hc : k * j * k⁻¹ * j⁻¹ ∈ P := by
          have := Subgroup.commutator_mem_commutator hk (hJY hj)
          rw [commutatorElement_def] at this
          exact hO2Y (Subgroup.mem_inf.mp (hKYc this)).2
        have e : (MulAut.conj k).toMonoidHom j = (k * j * k⁻¹ * j⁻¹) * j := by
          simp [MulAut.conj_apply]
        rw [e, sup_comm]
        exact Subgroup.mul_mem_sup hc hj
      have hle : (H₀ ⊔ P).map (MulAut.conj k).toMonoidHom ≤ H₀ ⊔ P := by
        rw [Subgroup.map_sup, hH₀eq, Subgroup.map_sup, hkL, hkP]
        exact sup_le (sup_le (le_sup_left.trans le_sup_left)
          (hkJ.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))) le_sup_right
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    have hPH : P ≤ Subgroup.normalizer (H₀ : Set G) :=
      (s.pCoreOf_M_le.trans ((pCoreOf_le 2 _).trans inf_le_left)).trans
        (CFSG.Quasithin.le_normalizer_conjClosure L H)
    have hO2 : oTwoUpper (H₀ ⊔ P) = H₀ :=
      le_antisymm (L4212.oTwoUpper_sup_le hPH (pCoreOf_isPGroup 2 M))
        (L4212.le_oTwoUpper_of_perfect le_sup_left s.H0_perfect)
    have hKH₀ : K ≤ Subgroup.normalizer (H₀ : Set G) := by
      intro k hk
      have := normalizer_le_normalizer_oTwoUpper _ (hKN hk)
      rwa [hO2] at this
    rw [← s.lemma_4_2_8 c]
    exact hKH₀
  refine ⟨hKY ▸ hJY, ?_, ?_⟩
  · intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hCm : C.map (MulAut.conj m).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (s.le_normalizer_C c hm)
    have hKm : K.map (MulAut.conj m).toMonoidHom ∈ cComp C := by
      have := cComp_map_mulEquiv (MulAut.conj m) hKcC
      rwa [hCm] at this
    have hpK : p ∣ Nat.card K := hKY ▸ hpY
    have hpKm : p ∣ Nat.card (K.map (MulAut.conj m).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]
      exact hpK
    exact huniq _ hKm K hKcC hpKm hpK
  · intro q hq hq2 hqL
    have : Fact q.Prime := ⟨hq⟩
    exact (CFSG.SectionRank.pRank_mono hq.one_lt hKC).trans (s.pRank_C_le_one hq2 hqL)

end Set425

end CFSG.Quasithin.H13.Ch4
