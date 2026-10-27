module

public import CFSG.Quasithin.Vol2.Ch4Sec4Hyp
public import CFSG.Quasithin.Vol2.Ch4Sec4Frattini
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

section Index

variable {X : Type} [Group X] [Finite X]

theorem relIndex_sup_dvd_card (H K : Subgroup X) [K.Normal] :
    H.relIndex (K ⊔ H) ∣ Nat.card K := by
  have h1 : H.relIndex (K ⊔ H) * Nat.card (H ⊓ (K ⊔ H) : Subgroup X) =
      Nat.card (K ⊔ H : Subgroup X) := Subgroup.relIndex_mul_card H (K ⊔ H)
  have h2 : K.relIndex (K ⊔ H) * Nat.card (K ⊓ (K ⊔ H) : Subgroup X) =
      Nat.card (K ⊔ H : Subgroup X) := Subgroup.relIndex_mul_card K (K ⊔ H)
  have h3 : K.relIndex H * Nat.card (K ⊓ H : Subgroup X) = Nat.card H :=
    Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.2 le_sup_right] at h1
  rw [inf_eq_left.2 le_sup_left, Subgroup.relIndex_sup_left] at h2
  have hpos : 0 < K.relIndex H := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at h3
    exact (Nat.card_pos (α := H)).ne' h3.symm
  refine ⟨Nat.card (K ⊓ H : Subgroup X), ?_⟩
  have key : K.relIndex H * (H.relIndex (K ⊔ H) * Nat.card (K ⊓ H : Subgroup X)) =
      K.relIndex H * Nat.card K := by
    calc K.relIndex H * (H.relIndex (K ⊔ H) * Nat.card (K ⊓ H : Subgroup X))
        = H.relIndex (K ⊔ H) * (K.relIndex H * Nat.card (K ⊓ H : Subgroup X)) := by ring
      _ = H.relIndex (K ⊔ H) * Nat.card H := by rw [h3]
      _ = Nat.card (K ⊔ H : Subgroup X) := h1
      _ = K.relIndex H * Nat.card K := h2.symm
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm

theorem le_of_normal_of_coprime_index {H K : Subgroup X} [K.Normal]
    (h : Nat.Coprime (Nat.card K) H.index) : K ≤ H := by
  have h1 := relIndex_sup_dvd_card H K
  have h2 : H.relIndex (K ⊔ H) ∣ H.index := Subgroup.relIndex_dvd_index_of_le le_sup_right
  have h3 : H.relIndex (K ⊔ H) = 1 := Nat.eq_one_of_dvd_coprimes h h1 h2
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h3)

omit [Finite X] in
theorem pCore_eq_open_pCore (p : ℕ) : CFSG.pCore p X = CFSG.Open.pCore p X :=
  (CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup (G := X) p).symm

omit [Finite X] in
theorem pCore_quotient_pCore_eq_bot (p : ℕ) :
    CFSG.pCore p (X ⧸ CFSG.pCore p X) = ⊥ := by
  set N := CFSG.pCore p X with hN
  set K := (CFSG.pCore p (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKp : IsPGroup p ↥K := by
    intro k
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := p) (G := X ⧸ N)
      ⟨QuotientGroup.mk' N k, k.2⟩
    have h1 : (k : X) ^ p ^ a ∈ N := by
      have h2 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h2
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
      exact h2
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := p) (G := X) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
    exact h3
  have hKN : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).2 (hKN hx)

end Index

theorem normal_sup_pCore_two {X : Type} [Group X] [Finite X] (hX : Group.IsSolvable X)
    {B : Subgroup X} [IsMulCommutative ↥B] {k : ℕ} (hBidx : B.index = 2 ^ k) :
    (B ⊔ CFSG.pCore 2 X).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 X with hN
  have hπs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hY : Group.IsSolvable (X ⧸ N) := by
    have := hX
    infer_instance
  have hO2 : CFSG.pCore 2 (X ⧸ N) = ⊥ := pCore_quotient_pCore_eq_bot 2
  set Bb := B.map (QuotientGroup.mk' N) with hBb
  have hBbidx : Bb.index ∣ 2 ^ k := hBidx ▸ Subgroup.index_map_dvd B hπs
  have hFB : CFSG.fittingSubgroup (X ⧸ N) ≤ Bb := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p.1.1).Prime := Nat.prime_of_mem_primeFactors p.1.2
    by_cases hp2 : p.1.1 = 2
    · rw [hp2, hO2]
      exact bot_le
    · have : Fact (p.1.1).Prime := ⟨hp⟩
      apply le_of_normal_of_coprime_index
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := p.1.1) (G := X ⧸ N))
      rw [hm]
      exact Nat.Coprime.coprime_dvd_right hBbidx
        (Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hBC : Bb ≤ Subgroup.centralizer (CFSG.fittingSubgroup (X ⧸ N) : Set (X ⧸ N)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact congrArg Subtype.val (mul_comm (⟨f, hFB hf⟩ : ↥Bb) ⟨b, hb⟩)
  have hBF : Bb ≤ CFSG.fittingSubgroup (X ⧸ N) :=
    hBC.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hY)
  have hBbn : Bb.Normal := by
    rw [le_antisymm hBF hFB]
    infer_instance
  have hpre : Bb.comap (QuotientGroup.mk' N) = B ⊔ N := by
    rw [hBb, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [← hpre]
  exact hBbn.comap _

variable {G : Type} [Group G]

theorem le_normalizer_map_subtype_of_normal (Y : Subgroup G) (R : Subgroup ↥Y) [R.Normal] :
    Y ≤ Subgroup.normalizer ((R.map Y.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := R) Y.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem eq_commutator_sup_of_wielandt (hW : WielandtCoprimeProduct) [Finite G]
    {Tp B : Subgroup G} (hTp : IsPGroup 2 ↥Tp) [IsMulCommutative ↥B] (hBodd : Odd (Nat.card B))
    (hBT : (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G)) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : ((Tp ⊔ B : Subgroup G) : Set G) = (Tp : Set G) * (B : Set G) :=
    coe_sup_of_mul_comm hBT
  have hTpX : Tp ≤ Tp ⊔ B := le_sup_left
  have hBX : B ≤ Tp ⊔ B := le_sup_right
  have hTB : Tp ⊓ B = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hTp hBodd
  have hcardTp : Nat.card (Tp.subgroupOf (Tp ⊔ B)) = Nat.card Tp :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTpX).toEquiv
  have hcardB : Nat.card (B.subgroupOf (Tp ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  have hmulX : ((Tp.subgroupOf (Tp ⊔ B) : Subgroup ↥(Tp ⊔ B)) : Set ↥(Tp ⊔ B)) *
      ((B.subgroupOf (Tp ⊔ B) : Subgroup ↥(Tp ⊔ B)) : Set ↥(Tp ⊔ B)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : (x : G) ∈ (Tp : Set G) * (B : Set G) := hX ▸ x.2
    obtain ⟨t, ht, b, hb, he⟩ := hx
    exact ⟨⟨t, hTpX ht⟩, ht, ⟨b, hBX hb⟩, hb, Subtype.ext he⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hTp
  have hsolv : Group.IsSolvable ↥(Tp ⊔ B) := by
    have hnilT : Group.IsNilpotent ↥(Tp.subgroupOf (Tp ⊔ B)) :=
      (hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTpX).symm).isNilpotent
    have hnilB : Group.IsNilpotent ↥(B.subgroupOf (Tp ⊔ B)) := inferInstance
    refine hW ↥(Tp ⊔ B) _ _ hnilT hnilB ?_ hmulX
    rw [hcardTp, hcardB, ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hBodd)
  have hinf : Tp.subgroupOf (Tp ⊔ B) ⊓ B.subgroupOf (Tp ⊔ B) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ Tp ⊓ B := ⟨hx.1, hx.2⟩
    rw [hTB] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext ((Subgroup.mem_bot).1 h1))
  have hc : Subgroup.IsComplement' (Tp.subgroupOf (Tp ⊔ B)) (B.subgroupOf (Tp ⊔ B)) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hinf) hmulX
  have hBidx : (B.subgroupOf (Tp ⊔ B)).index = 2 ^ a := by
    rw [hc.index_eq_card, hcardTp, ha]
  have hBQn := normal_sup_pCore_two hsolv hBidx
  have hmap : (B.subgroupOf (Tp ⊔ B) ⊔ CFSG.pCore 2 ↥(Tp ⊔ B)).map (Tp ⊔ B).subtype =
      B ⊔ pCoreOf 2 (Tp ⊔ B) := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBX]
    rfl
  have hXBQ : Tp ⊔ B ≤ Subgroup.normalizer ((B ⊔ pCoreOf 2 (Tp ⊔ B) : Subgroup G) : Set G) := by
    rw [← hmap]
    exact le_normalizer_map_subtype_of_normal _ _
  have hQX : pCoreOf 2 (Tp ⊔ B) ≤ Tp ⊔ B := pCoreOf_le 2 _
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (Tp ⊔ B)) := pCoreOf_isPGroup 2 _
  have hXQ : Tp ⊔ B ≤ Subgroup.normalizer ((pCoreOf 2 (Tp ⊔ B) : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hQT : pCoreOf 2 (Tp ⊔ B) ≤ Tp := by
    intro x hx
    have hx' : x ∈ (Tp : Set G) * (B : Set G) := hX ▸ hQX hx
    obtain ⟨t, ht, b, hb, rfl⟩ := hx'
    have hTQ2 : IsPGroup 2 ↥(Tp ⊔ pCoreOf 2 (Tp ⊔ B)) :=
      IsPGroup.to_sup_of_normal_right' hTp hQ2 (hTpX.trans hXQ)
    have hb' : b ∈ Tp ⊔ pCoreOf 2 (Tp ⊔ B) := by
      have he : b = t⁻¹ * (t * b) := by group
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Tp.inv_mem ht)) (Subgroup.mem_sup_right hx)
    have hb1 : b ∈ (Tp ⊔ pCoreOf 2 (Tp ⊔ B)) ⊓ B := ⟨hb', hb⟩
    rw [inf_eq_bot_of_isPGroup_two_of_odd hTQ2 hBodd] at hb1
    rw [(Subgroup.mem_bot).1 hb1]
    simpa using ht
  have hBQ : B ≤ Subgroup.normalizer ((pCoreOf 2 (Tp ⊔ B) : Subgroup G) : Set G) := hBX.trans hXQ
  have hcomm : ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ≤ pCoreOf 2 (Tp ⊔ B) :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hBQ
  have hQdec : pCoreOf 2 (Tp ⊔ B) ≤
      (pCoreOf 2 (Tp ⊔ B) ⊓ Subgroup.centralizer (B : Set G)) ⊔ ⁅pCoreOf 2 (Tp ⊔ B), B⁆ :=
    le_inf_centralizer_sup (hQ2.to_le hcomm) hBodd hcomm
      (Subgroup.normalizer_commutator_ge_left _ _) (Subgroup.normalizer_commutator_ge_right _ _)
      le_rfl
  have hCT : pCoreOf 2 (Tp ⊔ B) ⊓ Subgroup.centralizer (B : Set G) ≤
      Tp ⊓ Subgroup.normalizer (B : Set G) :=
    inf_le_inf hQT (Subgroup.centralizer_le_normalizer _)
  have hQle : pCoreOf 2 (Tp ⊔ B) ≤
      ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) := by
    refine hQdec.trans ?_
    rw [sup_comm]
    exact sup_le_sup_left hCT _
  apply le_antisymm
  ·
    intro t ht
    have htX : t ∈ Tp ⊔ B := hTpX ht
    have hmB : B.map (MulAut.conj t).toMonoidHom ≤ B ⊔ pCoreOf 2 (Tp ⊔ B) := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 (hXBQ htX) b).1 (Subgroup.mem_sup_left hb)
    obtain ⟨q, hq, hqt⟩ := exists_mul_mem_normalizer hQ2 hBodd hBQ (hXQ htX) hmB
    have hqtTB : q * t ∈ Tp ⊓ Subgroup.normalizer (B : Set G) := ⟨Tp.mul_mem (hQT hq) ht, hqt⟩
    have he : t = q⁻¹ * (q * t) := by group
    rw [he]
    exact Subgroup.mul_mem _ (hQle (inv_mem hq)) (Subgroup.mem_sup_right hqtTB)
  · exact sup_le (hcomm.trans hQT) inf_le_left

variable [Finite G] {T M L B Tp : Subgroup G}

theorem lemma_4_4_4_core_of (hW : WielandtCoprimeProduct) (h : Hyp4_4_1Core G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) := by
  have := h.B_comm
  exact eq_commutator_sup_of_wielandt hW (h.sylow.1.to_le h.Tp_le) h.B_odd h.mul_comm_Tp

theorem lemma_4_4_4_of (hW : WielandtCoprimeProduct) (h : Hyp4_4_1Two G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) :=
  lemma_4_4_4_core_of hW h.toHyp4_4_1Core

theorem lemma_4_4_4_orbit_of (hW : WielandtCoprimeProduct) (h : Hyp4_4_1TwoOrbit G T M L B Tp) :
    Tp = ⁅pCoreOf 2 (Tp ⊔ B), B⁆ ⊔ (Tp ⊓ Subgroup.normalizer (B : Set G)) :=
  lemma_4_4_4_core_of hW h.toHyp4_4_1Core

end CFSG.Quasithin.H13
