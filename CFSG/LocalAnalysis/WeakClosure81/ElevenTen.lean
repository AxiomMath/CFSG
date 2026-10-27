module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenNine
public import CFSG.LocalAnalysis.WeakClosure81.ElevenSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open Matrix
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)
open CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.SL2Modules

variable {G : Type} [Group G] [Finite G]

private theorem eleven_ten_inf_centralizer {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q) (hU : U ∈ deltaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    V ⊓ Subgroup.centralizer (L : Set G) = U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hUleC : U ≤ C := by
    refine le_inf hU.1.1 ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hL.1 hl) u hu).symm
  have hCleV : C ≤ V := inf_le_left
  have hLleCC : L ≤ Subgroup.centralizer (C : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 l hl).symm
  have hCnot : ¬ Subgroup.centralizer (C : Set G) ≤ M := fun h => hLM (hLleCC.trans h)
  have h1 : rMV M V ≤ (E3.mQuot V C : ℕ∞) := iInf₂_le C ⟨hCleV, hCnot⟩
  have h2 : (E3.mQuot V C : ℕ∞) ≤ (E3.mQuot V U : ℕ∞) := by
    exact_mod_cast E3.mQuot_mono hUleC
  have hCeqU : E3.mQuot V C = E3.mQuot V U :=
    ENat.natCast_inj.mp (le_antisymm h2 (hU.2.trans_le h1))
  have hadd := E3.mQuot_add (V := V) (U := U) (U' := C) hUleC hCleV
  have hzero : E3.mQuot C U = 0 := by
    rw [hCeqU] at hadd
    omega
  have hCpg : IsPGroup 2 C := hVpg.to_le hCleV
  exact ((E3.mQuot_eq_zero_iff hCpg hUleC).1 hzero).symm

private theorem eleven_ten_rMV_eq
    {M V Q U L D : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ deltaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hD : IsHallTwoPrimeOf D (L ⊓ M)) :
    rMV M V = (n : ℕ∞) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hset.isElemAbelian
  have hCV : V ⊓ Subgroup.centralizer (D : Set G) = U :=
    (eleven_nine_inf_centralizer_hall hset hU.1 hL hLM h78 hD).trans
      (eleven_ten_inf_centralizer hset hU hL hLM h78)
  have hDV : D ≤ Subgroup.normalizer (V : Set G) :=
    hD.1.trans (inf_le_right.trans hset.normal)
  have hVab : ∀ x y : ↥V, x * y = y * x := fun x y =>
    Subtype.ext (B2F.isElemAbelian_comm hset.isElemAbelian x.2 y.2)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card V) := by
    obtain ⟨k, hk⟩ := hVpg.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hD.2.1.not_two_dvd_nat).symm
  obtain ⟨hsup, hdisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp V D hDV hVab hcop
  have hcomm_le_V : ⁅V, D⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    have hdv : d * v * d⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hDV hd) v).mp hv
    rw [show ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ from by group]
    exact V.mul_mem hv (V.inv_mem hdv)
  have hB : (⁅V, D⁆ : Subgroup G) ≤
      Subgroup.normalizer ((V ⊓ Subgroup.centralizer (D : Set G)) : Set G) := by
    refine hcomm_le_V.trans ?_
    refine (show V ≤ Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (D : Set G)) : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm hset.isElemAbelian (Subgroup.mem_inf.mp hy).1 hx
  have hcard := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
    (A := V ⊓ Subgroup.centralizer (D : Set G)) (B := ⁅V, D⁆) hB
  rw [hsup, hdisj.eq_bot, Subgroup.card_bot, mul_one] at hcard
  rw [hCV, eleven_nine_card_commutator_hall hset hU.1 hL hLM h78 hD] at hcard
  have hmul : 2 ^ E3.mQuot V U * Nat.card U = 2 ^ n * Nat.card U := by
    rw [← E3.card_eq_two_pow_mul hVpg hU.1.1, hcard, mul_comm]
  have hmQuot : E3.mQuot V U = n :=
    Nat.pow_right_injective (le_refl 2)
      (Nat.mul_right_cancel (Nat.card_pos (α := U)) hmul)
  rw [← hU.2, hmQuot]

private theorem eleven_ten_hall_structure
    {M V Q U L X : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ deltaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) (hX : IsHallTwoPrimeOf X (L ⊓ M)) :
    IsCyclic ↥X ∧ Nat.card X = 2 ^ n - 1 ∧ V ⊓ Subgroup.centralizer (X : Set G) = U ∧
      ActsRegularlyOn X (nonIdentity ⁅V, X⁆) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc := eleven_nine_isCyclic_hall hset hU.1 hL hLM h78 hX
  have hcard := eleven_nine_card_hall hset hU.1 hL hLM h78 hX
  have hCVX : V ⊓ Subgroup.centralizer (X : Set G) = U :=
    (eleven_nine_inf_centralizer_hall hset hU.1 hL hLM h78 hX).trans
      (eleven_ten_inf_centralizer hset hU hL hLM h78)
  have hcardcomm := eleven_nine_card_commutator_hall hset hU.1 hL hLM h78 hX
  have hfreeBot : ∀ d ∈ X, d ≠ 1 → ⁅V, X⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ :=
    eleven_nine_commutator_hall_inf_centralizer hset hU.1 hL hLM h78 hX
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := hX.1.trans (inf_le_right.trans hset.normal)
  have hXnorm : X ≤ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hXV
  have hY : ∀ a ∈ X, ∀ y ∈ ⁅V, X⁆, a⁻¹ * y * a ∈ ⁅V, X⁆ := fun a ha y hy =>
    (by simpa using (Subgroup.mem_normalizer_iff.mp (hXnorm (X.inv_mem ha)) y).mp hy)
  have hfree : ∀ a ∈ X, a ≠ 1 → ∀ y ∈ ⁅V, X⁆, a⁻¹ * y * a = y → y = 1 := by
    intro a ha ha1 y hy hay
    have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : a * (a⁻¹ * y * a) = a * y := congrArg (fun z => a * z) hay
      calc y * a = a * (a⁻¹ * y * a) := by group
        _ = a * y := h
    have : y ∈ ⁅V, X⁆ ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_inf.mpr ⟨hy, hyC⟩
    rw [hfreeBot a ha ha1, Subgroup.mem_bot] at this
    exact this
  have hcard' : Nat.card (⁅V, X⁆ : Subgroup G) = Nat.card X + 1 := by
    rw [hcardcomm, hcard]
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (le_of_lt h78.1)
    omega
  refine ⟨hcyc, hcard, hCVX, ?_, ?_, ?_⟩
  · intro b hb z hz
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (hXnorm (X.inv_mem hb)) z).mp hz.1
    · intro h0
      exact hz.2 (by
        calc z = b * (b⁻¹ * z * b) * b⁻¹ := by group
          _ = b * 1 * b⁻¹ := by rw [h0]
          _ = 1 := by group)
  · intro z hz z' hz'
    exact CFSG.QuasithinUnique.Lin2.transitive_of_free_of_card hY hfree hcard'
      hz.1 hz.2 hz'.1 hz'.2
  · intro z hz b hb hbz
    by_contra hb1
    exact hz.2 (hfree b hb hb1 z hz.1 hbz)

private theorem eleven_ten_map_normalizer_eq {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) {H : Subgroup G} (hker : f.ker ≤ H) :
    (Subgroup.normalizer (H : Set G)).map f =
      Subgroup.normalizer ((H.map f : Subgroup G') : Set G') := by
  have hcomap : (Subgroup.normalizer ((H.map f : Subgroup G') : Set G')).comap f =
      Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hf, Subgroup.comap_map_eq_self hker]
  have hmap := congrArg (Subgroup.map f) hcomap
  rw [Subgroup.map_comap_eq_self_of_surjective hf] at hmap
  exact hmap.symm

private theorem eleven_ten_relIndex
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ deltaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78 : IsLTwoBlockType L n) :
    (L ⊓ M).relIndex L = 2 ^ n + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  obtain ⟨⟨hS, hBeq⟩, ⟨S, hSmap⟩⟩ := eleven_nine_one hset hU.1 hL hLM h78
  let Lq := ↥L ⧸ CFSG.pCore 2 ↥L
  let SL2 := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  have hO2LM : oTwoIn L ≤ L ⊓ M := by
    obtain ⟨T, hT⟩ := sylow_of_isSylowOf hS
    haveI : (CFSG.pCore 2 ↥L).Normal := pCore_normal
    have hpc : CFSG.pCore 2 ↥L ≤ (T : Subgroup ↥L) :=
      IsPGroup.le_sylow_of_normal pCore_isPGroup T
    have ho2le : oTwoIn L ≤ L ⊓ Q := by
      calc oTwoIn L = (CFSG.pCore 2 ↥L).map L.subtype := oTwoIn_eq_map L
        _ ≤ (T : Subgroup ↥L).map L.subtype := Subgroup.map_mono hpc
        _ = L ⊓ Q := by rw [hT, Subgroup.map_subgroupOf_eq_of_le hS.1]
    exact ho2le.trans (le_inf inf_le_left (inf_le_right.trans (hset.sylowQ.1.trans inf_le_left)))
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ (L ⊓ M).subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO2LM (Subgroup.mem_map_of_mem L.subtype hx))
  have h1 : ((L ⊓ M).subgroupOf L).index =
      (Subgroup.normalizer ((S : Subgroup Lq) : Set Lq)).index := by
    rw [← Subgroup.index_map_eq (H := (L ⊓ M).subgroupOf L)
      (QuotientGroup.mk'_surjective _) hker, hSmap]
  obtain ⟨φ, -, -⟩ := h78.2.1
  let f : Lq →* SL2 := φ.toMonoidHom
  have hf : Function.Surjective f := φ.surjective
  let P : Sylow 2 SL2 := S.mapSurjective hf
  have hkerf : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr φ.injective
  have h2 : (Subgroup.normalizer ((S : Subgroup Lq) : Set Lq)).index =
      (Subgroup.normalizer ((P : Subgroup SL2) : Set SL2)).index := by
    have hP : (P : Subgroup SL2) = (S : Subgroup Lq).map f := rfl
    have hle : f.ker ≤ Subgroup.normalizer ((S : Subgroup Lq) : Set Lq) := by
      rw [hkerf]; exact bot_le
    have hmap := eleven_ten_map_normalizer_eq hf (H := (S : Subgroup Lq))
      (by rw [hkerf]; exact bot_le)
    rw [hP, ← hmap]
    exact (Subgroup.index_map_eq (H := Subgroup.normalizer ((S : Subgroup Lq) : Set Lq))
      hf hle).symm
  have h3 : (Subgroup.normalizer ((P : Subgroup SL2) : Set SL2)).index =
      Fintype.card (GaloisField 2 n) + 1 := by
    have hbig := sl2_defining_characteristic_Sylow_normalizer_maximal_Borel
      (F := GaloisField 2 n) (p := 2)
    obtain ⟨g, -, -, -, -, hidx⟩ := hbig.2.2.2.2.2.2.2 P
    exact hidx
  calc (L ⊓ M).relIndex L
      = ((L ⊓ M).subgroupOf L).index := rfl
    _ = (Subgroup.normalizer ((S : Subgroup Lq) : Set Lq)).index := h1
    _ = (Subgroup.normalizer ((P : Subgroup SL2) : Set SL2)).index := h2
    _ = Fintype.card (GaloisField 2 n) + 1 := h3
    _ = 2 ^ n + 1 := by
      rw [← Nat.card_eq_fintype_card,
        GaloisField.card 2 n (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78.1))]

private theorem eleven_ten_unique
    {M V Q U L : Subgroup G} {n : ℕ}
    (hset : Setting11 M V Q)
    (hU : U ∈ deltaEleven M V)
    (h78 : ∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
      ∃ n : ℕ, IsLTwoBlockType L' n)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M)
    (h78L : IsLTwoBlockType L n) :
    ∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
      L' = L := by
  intro L' hL' hL'M
  by_contra hne
  obtain ⟨n', h78'⟩ := h78 L' hL' hL'M
  have hchar : IsCharacteristicP 2 ↥(Subgroup.centralizer (U : Set G)) :=
    eleven_e hset.charTwo hU.1.2.1
      ((B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hU.1.1)
  have hcomm : ⁅L, L'⁆ = ⊥ :=
    distinct_blocks_commute_of_isBlockOfInX hchar hL hL' (Ne.symm hne)
  have hCL : L ≤ Subgroup.centralizer (L' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hleU : V ⊓ blockU L' ≤ U := by
    rw [← eleven_ten_inf_centralizer hset hU hL hLM h78L]
    refine le_inf inf_le_left ?_
    intro x hx
    obtain ⟨-, hxU'⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hCL hl) x (blockU_le L' hxU')).symm
  obtain ⟨D', hD'⟩ := eleven_nine_exists_hall hset hU.1 hL' hL'M h78'
  have hCV' : V ⊓ Subgroup.centralizer (L' : Set G) = U :=
    eleven_ten_inf_centralizer hset hU hL' hL'M h78'
  have hVU : V ≤ U := by
    rw [eleven_nine_eq_sup_inf_blockU hset hU.1 hL' hL'M h78' hD']
    exact sup_le (le_of_eq hCV') hleU
  have hVeqU : V = U := le_antisymm hVU hU.1.1
  have hRV : rMV M V = (n' : ℕ∞) := eleven_ten_rMV_eq hset hU hL' hL'M h78' hD'
  have hzero : E3.mQuot V U = 0 := by rw [hVeqU, E3.mQuot_self]
  have hfin : n' = 0 := by
    have h1 : (n' : ℕ∞) = (E3.mQuot V U : ℕ∞) := by rw [← hRV, hU.2]
    rw [hzero] at h1
    exact ENat.natCast_inj.mp h1
  exact absurd hfin (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h78'.1))

theorem eleven_ten {M V Q U L : Subgroup G}
    (hset : Setting11 M V Q)
    (hU : U ∈ deltaEleven M V)
    (h78 : ∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
      ∃ n : ℕ, IsLTwoBlockType L' n)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M) :
    ∃ n : ℕ, 1 < n ∧ IsNaturalSLTwoModule ↥L n ∧ rMV M V = (n : ℕ∞) ∧
      V ⊓ Subgroup.centralizer (L : Set G) = U ∧
      (∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
        L' = L) ∧
      (L ⊓ M).relIndex L = 2 ^ n + 1 ∧
      (∃ X : Subgroup G, IsHallTwoPrimeOf X (L ⊓ M)) ∧
      ∀ X : Subgroup G, IsHallTwoPrimeOf X (L ⊓ M) → IsCyclic ↥X ∧ Nat.card X = 2 ^ n - 1 ∧
        V ⊓ Subgroup.centralizer (X : Set G) = U ∧ ActsRegularlyOn X (nonIdentity ⁅V, X⁆) := by
  obtain ⟨n, h78L⟩ := h78 L hL hLM
  obtain ⟨D, hD⟩ := eleven_nine_exists_hall hset hU.1 hL hLM h78L
  exact ⟨n, h78L.1, h78L.2.1, eleven_ten_rMV_eq hset hU hL hLM h78L hD,
    eleven_ten_inf_centralizer hset hU hL hLM h78L,
    eleven_ten_unique hset hU h78 hL hLM h78L,
    eleven_ten_relIndex hset hU hL hLM h78L,
    ⟨D, hD⟩,
    fun X hX => eleven_ten_hall_structure hset hU hL hLM h78L hX⟩

theorem eleven_ten_of_one_lt {M V Q U L : Subgroup G}
    (hset : Setting11 M V Q)
    (hr : 1 < rMV M V) (hm : 1 < mBar M ⊥ V hset.isElemAbelian) (hU : U ∈ deltaEleven M V)
    (hL : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L) (hLM : ¬ L ≤ M) :
    ∃ n : ℕ, 1 < n ∧ IsNaturalSLTwoModule ↥L n ∧ rMV M V = (n : ℕ∞) ∧
      V ⊓ Subgroup.centralizer (L : Set G) = U ∧
      (∀ L' : Subgroup G, IsBlockOfInX (Subgroup.centralizer (U : Set G)) L' → ¬ L' ≤ M →
        L' = L) ∧
      (L ⊓ M).relIndex L = 2 ^ n + 1 ∧
      (∃ X : Subgroup G, IsHallTwoPrimeOf X (L ⊓ M)) ∧
      ∀ X : Subgroup G, IsHallTwoPrimeOf X (L ⊓ M) → IsCyclic ↥X ∧ Nat.card X = 2 ^ n - 1 ∧
        V ⊓ Subgroup.centralizer (X : Set G) = U ∧ ActsRegularlyOn X (nonIdentity ⁅V, X⁆) := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hU
  refine eleven_ten hset hU (fun L' hL' hL'M => ?_) hL hLM
  obtain ⟨n, hn, hnat⟩ := eleven_eight hset hr hm hUΓ hL' hL'M
  exact ⟨n, hn, hnat, eleven_seven hset hr hm hUΓ hL' hL'M⟩

end CFSG.LocalAnalysis.WeakClosure81
