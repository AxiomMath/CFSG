module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutOmega
import CFSG.GroupTheory.CyclicAutOmega
import CFSG.GroupTheory.PComponentInvert
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPCube
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThreeGroup
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
import CFSG.RankThree.PartTwo.KFacts.K72Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isCyclic_of_le_range_conj)

variable {G : Type} [Group G] [Finite G]

private theorem exists_inverting_of_mod {K N C A : Subgroup G} (hKN : K ≤ normalizer (N : Set G))
    (hCK : C ≤ K) (hcop : ¬ 3 ∣ Nat.card N) (hAC : A ≤ C) (hA3 : Nat.card A = 3) {c : G}
    (hcC : c ∈ C) (hmod : ∀ a ∈ A, (c * a * c⁻¹) * a ∈ N) :
    ∃ t ∈ C, ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAN : A ⊓ N = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
    rw [hA3]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hcop)).eq_bot
  set D : Subgroup G := N ⊓ C with hD
  have hDnorm : C ≤ normalizer (D : Set G) :=
    (le_inf (hCK.trans hKN) le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hADdisj : Disjoint D A := disjoint_iff.2 (eq_bot_iff.2
    ((inf_le_inf_right A inf_le_left).trans (by rw [inf_comm, hAN])))
  have hADcard : Nat.card (A ⊔ D : Subgroup G) = 3 * Nat.card D := by
    rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D A
      (hAC.trans hDnorm) hADdisj, hA3, Nat.mul_comm]
  have hPAD : A.map (MulAut.conj c).toMonoidHom ≤ A ⊔ D := by
    rintro _ ⟨a, ha, rfl⟩
    have hnN : a * (c * a * c⁻¹) ∈ N := by
      have h := (mem_normalizer_iff.1 (hKN (hCK (hAC ha))) _).1 (hmod a ha)
      rwa [show a * ((c * a * c⁻¹) * a) * a⁻¹ = a * (c * a * c⁻¹) by group] at h
    have hcaC : a * (c * a * c⁻¹) ∈ C :=
      C.mul_mem (hAC ha) (C.mul_mem (C.mul_mem hcC (hAC ha)) (C.inv_mem hcC))
    change c * a * c⁻¹ ∈ A ⊔ D
    rw [show c * a * c⁻¹ = a⁻¹ * (a * (c * a * c⁻¹)) by group]
    exact Subgroup.mul_mem_sup (A.inv_mem ha) ⟨hnN, hcaC⟩
  obtain ⟨d, hdD, hconj⟩ := CFSG.GroupTheory.exists_mem_inf_conj_eq_of_isSylowOf hAC hDnorm
    hADcard (fun h => hcop (h.trans (Subgroup.card_dvd_of_le inf_le_left))) hA3
    (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hA3])
    ((IsPGroup.iff_card.2 ⟨1, by rw [hA3]; norm_num⟩).map _) hPAD
  exact CFSG.GroupTheory.exists_inverting_of_conj_eq hKN (hAC.trans hCK) hcC hdD.1 hdD.2 hAN
    hmod hconj

theorem exists_inverting {M L B : Subgroup G} {b₀ a : G} (hL : L ∈ calC M)
    (hr : CFSG.Open.pRank 3 L = 1)
    (hsh : R8107Shape.ThinShape (Bar2 L) ∨ ∃ n : ℕ, IsU3 (Bar2 L) n)
    (hBp : IsPGroup 3 ↥(zpowers b₀ ⊔ B)) (hBL : zpowers b₀ ⊔ B ≤ normalizer (L : Set G))
    (hb₀N : b₀ ∈ normalizer (L : Set G)) (hb₀3 : b₀ ^ 3 = 1)
    (hb₀ : ¬ IsInnerAut (UC6S846.rhoL L ⟨b₀, hb₀N⟩) ∨ UC6S846.rhoL L ⟨b₀, hb₀N⟩ = 1)
    (hB : ∀ u (hu : u ∈ normalizer (L : Set G)), u ∈ B → UC6S846.rhoL L ⟨u, hu⟩ = 1)
    (haL : a ∈ L) (ha3 : orderOf a = 3)
    (hac : a ∈ centralizer ((zpowers b₀ ⊔ B : Subgroup G) : Set G)) :
    ∃ t ∈ L ⊓ centralizer ((zpowers b₀ ⊔ B : Subgroup G) : Set G), t * a * t⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ¬ 3 ∣ Nat.card (pCoreOf 2 L) :=
    P2251c.not_dvd_card_of_isPGroup_two (UC6S846.isPGroup_pCoreOf L) Nat.prime_three (by norm_num)
  set ā : Bar2 L := QuotientGroup.mk (⟨a, haL⟩ : ↥L) with hā
  have hā1 : ā ≠ 1 := fun h => P2251c.not_mem_of_orderOf_eq_three (UC6S846.isPGroup_pCoreOf L)
    ha3 (mem_map.2 ⟨⟨a, haL⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩)
  have hā3 : ā ^ 3 = 1 := by
    rw [hā, ← QuotientGroup.mk_pow, show (⟨a, haL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow]; exact ha3 ▸ pow_orderOf_eq_one a), QuotientGroup.mk_one]
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 1 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num), hr]
  have hfix : UC6S846.rhoL L ⟨b₀, hb₀N⟩ ā = ā := by
    refine (UC6S846.rhoL_fix_iff L _ _).2 ?_
    have h := mem_centralizer_iff.1 hac b₀ (mem_sup_left (mem_zpowers b₀))
    change b₀ * a * b₀⁻¹ * a⁻¹ ∈ pCoreOf 2 L
    rw [h, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  obtain ⟨y, hy, hyā⟩ : ∃ y : Bar2 L, UC6S846.rhoL L ⟨b₀, hb₀N⟩ y = y ∧ y * ā * y⁻¹ = ā⁻¹ := by
    rcases hb₀ with hout | htriv
    · refine exists_inverting_of_fixed hsh h1 ?_ hout hā3 hā1 hfix
      rw [← map_pow, show (⟨b₀, hb₀N⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 from
        Subtype.ext hb₀3, map_one]
    · haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
      have hāp : IsPGroup 3 (zpowers ā) := IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, orderOf_eq_prime hā3 hā1, pow_one])
      obtain ⟨Q, hQ⟩ := hāp.exists_le_sylow
      haveI : IsCyclic (Q : Subgroup (Bar2 L)) :=
        RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one (by norm_num) h1.le Q
      have hāQ : ā ∈ (Q : Subgroup (Bar2 L)) := hQ (mem_zpowers ā)
      obtain ⟨n, -, hn⟩ := CFSG.GroupTheory.exists_mem_normalizer_conj_eq_inv_of_perfect Q
        (fun h0 => hā1 (by rwa [h0, Subgroup.mem_bot] at hāQ))
      refine ⟨n, by rw [htriv, MulAut.one_apply], hn ā ⟨⟨ā, hāQ⟩, Subgroup.subset_closure ?_, rfl⟩⟩
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hā3)
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hESt : zpowers b₀ ⊔ B ≤ ((MulAction.stabilizer (MulAut (Bar2 L))
      (QuotientGroup.mk y' : Bar2 L)).comap (UC6S846.rhoL L)).map
        (normalizer (L : Set G)).subtype :=
    sup_le (zpowers_le.2 ⟨⟨b₀, hb₀N⟩, hy, rfl⟩) fun u hu => ⟨⟨u, hBL (mem_sup_right hu)⟩, by
      change UC6S846.rhoL L _ (QuotientGroup.mk y') = _
      rw [hB u _ hu, MulAut.one_apply], rfl⟩
  have hq : ∀ u ∈ zpowers b₀ ⊔ B, (y' : G)⁻¹ * (u * y' * u⁻¹) ∈ pCoreOf 2 L := by
    intro u hu
    obtain ⟨⟨v, hvN⟩, hv, rfl⟩ := hESt hu
    have h := (mem_normalizer_iff.1 (UC6S846.normalizer_le_normalizer_pCoreOf L
      (le_normalizer (L.inv_mem y'.2))) _).1 ((UC6S846.rhoL_fix_iff L ⟨v, hvN⟩ y').1 hv)
    change (y' : G)⁻¹ * (v * y' * v⁻¹) ∈ pCoreOf 2 L
    rwa [show (y' : G)⁻¹ * (v * y' * v⁻¹ * (y' : G)⁻¹) * (y' : G)⁻¹⁻¹ =
      (y' : G)⁻¹ * (v * y' * v⁻¹) by group] at h
  obtain ⟨c, hcy, hcE⟩ := UC6.exists_fixed_in_coset_uc6 (zpowers b₀ ⊔ B) (pCoreOf 2 L) hBp hcop
    (fun x hx f hf => (mem_normalizer_iff.1
      (UC6S846.normalizer_le_normalizer_pCoreOf L (hBL hx)) f).1 hf) (y' : G) hq
  have hcL : c ∈ L := by
    simpa using L.mul_mem y'.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 L hcy)
  have hcC : c ∈ centralizer ((zpowers b₀ ⊔ B : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun u hu => by
      calc u * c = u * c * u⁻¹ * u := by group
        _ = c * u := by rw [hcE u hu]
  have hcbar : (QuotientGroup.mk (⟨c, hcL⟩ : ↥L) : Bar2 L) = QuotientGroup.mk y' :=
    (QuotientGroup.eq.2 ((mem_map_iff_mem L.subtype_injective).1
      (show L.subtype (y'⁻¹ * ⟨c, hcL⟩) ∈ pCoreOf 2 L from hcy))).symm
  have hmod : ∀ x ∈ zpowers a, (c * x * c⁻¹) * x ∈ pCoreOf 2 L := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    refine mem_map.2 ⟨⟨c, hcL⟩ * ⟨a, haL⟩ ^ k * (⟨c, hcL⟩ : ↥L)⁻¹ * ⟨a, haL⟩ ^ k, ?_, by simp⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, hcbar, ← conj_zpow, ← hā,
      hyā, inv_zpow, inv_mul_cancel]
  obtain ⟨t, htC, ht⟩ := exists_inverting_of_mod (K := L) (fun x hx =>
      UC6S846.normalizer_le_normalizer_pCoreOf L (le_normalizer hx)) inf_le_left hcop
    (zpowers_le.2 ⟨haL, hac⟩) (by rw [Nat.card_zpowers, ha3]) ⟨hcL, hcC⟩ hmod
  exact ⟨t, htC, ht a (mem_zpowers a)⟩

theorem exists_transvection {M L S : Subgroup G} {a₀ a₁ : G} (hL : L ∈ calC M)
    (hr : CFSG.Open.pRank 3 L = 1)
    (hsh : R8107Shape.ThinShape (Bar2 L) ∨ ∃ n : ℕ, IsU3 (Bar2 L) n)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M) (hSL : S ≤ normalizer (L : Set G))
    (ha₁ : a₁ ∈ S ⊓ L) (ha₁3 : orderOf a₁ = 3) (ha₀ : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (hout : ¬ IsInnerAut (UC6S846.rhoL L ⟨a₀, hSL ha₀⟩)) :
    ∃ x ∈ S ⊓ L, x * a₀ * x⁻¹ = a₀ * a₁ ∧ x * a₁ = a₁ * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := hS.isPGroup
  haveI hcyc : IsCyclic ↥(S ⊓ L) :=
    R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one hr inf_le_right hSp.to_inf_left
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 1 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num), hr]
  have hα3 : UC6S846.rhoL L ⟨a₀, hSL ha₀⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨a₀, hSL ha₀⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 from
      Subtype.ext ha₀3, map_one]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ L) L :=
    (hS.of_le le_sup_left (sup_le hS.le hL.1.le)).inf_of_le_normalizer le_sup_right
      (sup_le hSL le_normalizer)
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  obtain ⟨z, hzQ, hz⟩ := exists_ne_of_sylow hsh h1 hα3 hout
    (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  rw [Sylow.coe_mapSurjective] at hzQ
  obtain ⟨⟨s, hsL⟩, hsQ, rfl⟩ := hzQ
  have hs : s ∈ S ⊓ L := by
    rw [hQ] at hsQ
    exact hsQ
  have hN : a₀ ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer ha₀, hSL ha₀⟩
  have hwSL : a₀ * s * a₀⁻¹ * s⁻¹ ∈ S ⊓ L :=
    (S ⊓ L).mul_mem ((mem_normalizer_iff.1 hN s).1 hs) ((S ⊓ L).inv_mem hs)
  have hw1 : a₀ * s * a₀⁻¹ * s⁻¹ ≠ 1 := fun h => hz ((UC6S846.rhoL_fix_iff L _ ⟨s, hsL⟩).2 (by
    change a₀ * s * a₀⁻¹ * s⁻¹ ∈ pCoreOf 2 L
    rw [h]
    exact one_mem _))
  have hw3 : orderOf (a₀ * s * a₀⁻¹ * s⁻¹) = 3 := orderOf_eq_prime
    (CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27.commutator_pow_three_of_isCyclic hcyc
      hSp.to_inf_left hN ha₀3 hs) hw1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1
    (CFSG.AGLEmbedding.mem_zpowers_of_isCyclic_of_orderOf_eq_three hcyc hwSL ha₁ hw3 ha₁3)
  have ha₁c : a₁ ∈ centralizer (S : Set G) := le_centralizer_of_pRank_eq_one hr hSp hSL
    (zpowers_le.2 ha₁) (by rw [Nat.card_zpowers, ha₁3]) (mem_zpowers a₁)
  have hws : Commute (a₀ * s * a₀⁻¹ * s⁻¹) s :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := ↥(S ⊓ L))).mul_comm ⟨_, hwSL⟩ ⟨s, hs⟩)
  have hconj : a₀ * s ^ k * a₀⁻¹ = (a₀ * s * a₀⁻¹ * s⁻¹) ^ k * s ^ k := by
    rw [← conj_zpow, ← hws.mul_zpow]
    group
  refine ⟨s ^ (-k), zpow_mem hs _, ?_, mem_centralizer_iff.1 ha₁c _ (zpow_mem hs _).1⟩
  calc s ^ (-k) * a₀ * (s ^ (-k))⁻¹ = s ^ (-k) * (a₀ * s ^ k * a₀⁻¹) * a₀ := by group
    _ = (a₀ * s * a₀⁻¹ * s⁻¹) ^ k * a₀ := by rw [hconj, (hws.zpow_zpow k k).eq]; group
    _ = a₀ * a₁ := by rw [hk]; exact (mem_centralizer_iff.1 ha₁c a₀ ha₀).symm

theorem exists_outer_or_trivial {M L₁ L₂ S : Subgroup G} {a₀ a₂ : G} (hL₁ : L₁ ∈ calC M)
    (hL₂ : L₂ ∈ calC M) (hne : L₁ ≠ L₂) (hr₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hZ₂ : center (Bar2 L₂) = ⊥) (hSp : IsPGroup 3 S) (hS₁ : S ≤ normalizer (L₁ : Set G))
    (hS₂ : S ≤ normalizer (L₂ : Set G)) (ha₂ : a₂ ∈ S ⊓ L₂) (ha₂3 : orderOf a₂ = 3)
    (ha₀ : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1) (hout : ¬ IsInnerAut (UC6S846.rhoL L₁ ⟨a₀, hS₁ ha₀⟩)) :
    ∃ b, ∃ hb : b ∈ S, b ^ 3 = 1 ∧ ¬ IsInnerAut (UC6S846.rhoL L₁ ⟨b, hS₁ hb⟩) ∧
      (¬ IsInnerAut (UC6S846.rhoL L₂ ⟨b, hS₂ hb⟩) ∨ UC6S846.rhoL L₂ ⟨b, hS₂ hb⟩ = 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hin : IsInnerAut (UC6S846.rhoL L₂ ⟨a₀, hS₂ ha₀⟩)
  swap
  · exact ⟨a₀, ha₀, ha₀3, hout, Or.inl hin⟩
  by_cases h01 : UC6S846.rhoL L₂ ⟨a₀, hS₂ ha₀⟩ = 1
  · exact ⟨a₀, ha₀, ha₀3, hout, Or.inr h01⟩
  haveI : Finite (MulAut (Bar2 L₂)) := MulEquiv.finite_left
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L₂)) = 1 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num), hr₂]
  have hQc := isCyclic_of_le_range_conj
    (fun P => RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one (by norm_num) h1.le P)
    ((hSp.comap_subtype (K := normalizer (L₂ : Set G))).map (UC6S846.rhoL L₂)).to_inf_right
    (inf_le_left : (MulAut.conj : Bar2 L₂ →* MulAut (Bar2 L₂)).range ⊓ _ ≤ _)
  have hcube : ∀ y (hy : y ∈ S), y ^ 3 = 1 → UC6S846.rhoL L₂ ⟨y, hS₂ hy⟩ ^ 3 = 1 :=
    fun y hy hy3 => by
      rw [← map_pow, show (⟨y, hS₂ hy⟩ : ↥(normalizer (L₂ : Set G))) ^ 3 = 1 from
        Subtype.ext hy3, map_one]
  have ha₂3' : a₂ ^ 3 = 1 := ha₂3 ▸ pow_orderOf_eq_one a₂
  have ha₂1 : a₂ ≠ 1 := fun h => by rw [h, orderOf_one] at ha₂3; omega
  have hinner₂ : IsInnerAut (UC6S846.rhoL L₂ ⟨a₂, hS₂ ha₂.1⟩) :=
    ⟨_, (UC6S846.rhoL_inner L₂ a₂ ha₂.2).symm⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (CFSG.AGLEmbedding.mem_zpowers_of_isCyclic_of_orderOf_eq_three
    hQc ⟨hinner₂, ⟨a₂, hS₂ ha₂.1⟩, ha₂.1, rfl⟩ ⟨hin, ⟨a₀, hS₂ ha₀⟩, ha₀, rfl⟩
    (orderOf_eq_prime (hcube a₂ ha₂.1 ha₂3') (rhoL_ne_one_of_mem hZ₂ ha₂.2 ha₂3' ha₂1))
    (orderOf_eq_prime (hcube a₀ ha₀ ha₀3) h01))
  have hc : a₀ * a₂ = a₂ * a₀ := (mem_centralizer_iff.1 (le_centralizer_of_pRank_eq_one hr₂ hSp
    hS₂ (zpowers_le.2 ha₂) (by rw [Nat.card_zpowers, ha₂3]) (mem_zpowers a₂)) a₀ ha₀)
  have ha₂S : a₂ ∈ S := ha₂.1
  have hbS : a₀ * a₂ ^ (-j) ∈ S := S.mul_mem ha₀ (S.zpow_mem ha₂S _)
  have hsplit : ∀ (K : Subgroup G) (h : a₀ * a₂ ^ (-j) ∈ normalizer (K : Set G))
      (h₀ : a₀ ∈ normalizer (K : Set G)) (h₂ : a₂ ∈ normalizer (K : Set G)),
      UC6S846.rhoL K ⟨_, h⟩ = UC6S846.rhoL K ⟨a₀, h₀⟩ * UC6S846.rhoL K ⟨a₂, h₂⟩ ^ (-j) :=
    fun K h h₀ h₂ => by rw [← map_zpow, ← map_mul]; rfl
  refine ⟨a₀ * a₂ ^ (-j), hbS, ?_, ?_, Or.inr ?_⟩
  · rw [(Commute.zpow_right hc.symm.symm (-j)).mul_pow, ha₀3, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₂3', one_zpow]
  · rwa [hsplit L₁ _ (hS₁ ha₀) (hS₁ ha₂.1),
      rhoL_eq_one_of_mem hL₁ hL₂ hne ha₂.2 (hS₁ ha₂.1), one_zpow, mul_one]
  · rw [hsplit L₂ _ (hS₂ ha₀) (hS₂ ha₂.1), ← hj, ← zpow_add, add_neg_cancel, zpow_zero]

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out
