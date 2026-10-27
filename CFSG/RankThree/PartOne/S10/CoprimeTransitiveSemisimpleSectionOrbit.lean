module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
import CFSG.RankThree.PartOne.S10.TransitiveSemisimpleOddKernel
import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
import CFSG.RankThree.GroupTheory.SteinbergBMMinimalPerfectCover
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

namespace CoprimeSemisimpleOrbit

theorem coordSubgroup_normal {I : Type} [DecidableEq I] (T : I → Type) [∀ i, Group (T i)]
    (i : I) : (coordSubgroup T i).Normal :=
  ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    refine ⟨g i * s * (g i)⁻¹, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]⟩

theorem eq_mulSingle_of_mem_coordSubgroup {I : Type} [DecidableEq I] {T : I → Type}
    [∀ i, Group (T i)] {i : I} {y : ∀ i, T i} (hy : y ∈ coordSubgroup T i) :
    y = Pi.mulSingle i (y i) := by
  obtain ⟨t, rfl⟩ := hy
  simp [MonoidHom.mulSingle_apply]

theorem map_subtype_commutator {K : Type*} [Group K] (U : Subgroup K) :
    (commutator ↥U).map U.subtype = ⁅U, U⁆ := by
  have h : (⊤ : Subgroup U).map U.subtype = U := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [_root_.commutator_def, Subgroup.map_commutator, h]

theorem exists_component_family {J : Type*} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
    {I : Type} [Fintype I] [DecidableEq I] (T : I → Type) [∀ i, Group (T i)]
    [∀ i, Finite (T i)] [∀ i, IsSimpleGroup (T i)] (hnonab : ∀ i, ∃ a b : T i, a * b ≠ b * a)
    (ψ : K →* ∀ i, T i) (hψ : Function.Surjective ψ) (hcen : ∀ k : K, ψ k = 1 → k ∈ center K)
    (x : J)
    (htrans : ∀ i j : I, ∃ n : ℕ, ∀ k : K,
      ψ k ∈ coordSubgroup T i ↔ ψ (MulAut.conjNormal (x ^ n) k) ∈ coordSubgroup T j) :
    ∃ L : I → Subgroup J, (∀ i, IsComponent (L i)) ∧
      (∀ i, Nat.card (L i ⧸ center (L i)) = Nat.card (T i)) ∧ Function.Injective L ∧
      ∀ i j : I, ∃ n : ℕ, (L i).map (MulAut.conj (x ^ n)).toMonoidHom = L j := by
  classical
  let U : I → Subgroup K := fun i => (coordSubgroup T i).comap ψ
  have hUmem : ∀ (i : I) (k : K), k ∈ U i ↔ ψ k ∈ coordSubgroup T i := fun i k => Iff.rfl
  have hUn : ∀ i, (U i).Normal := fun i => by
    have := coordSubgroup_normal T i
    exact Subgroup.Normal.comap inferInstance ψ
  let f : ∀ i, ↥(U i) →* T i := fun i => (Pi.evalMonoidHom T i).comp (ψ.comp (U i).subtype)
  have hfapp : ∀ (i : I) (u : U i), f i u = ψ (u : K) i := fun i u => rfl
  have hfsurj : ∀ i, Function.Surjective (f i) := by
    intro i t
    obtain ⟨k, hk⟩ := hψ (Pi.mulSingle i t)
    refine ⟨⟨k, ?_⟩, ?_⟩
    · rw [hUmem, hk]
      exact ⟨t, rfl⟩
    · rw [hfapp]
      change ψ k i = t
      rw [hk]
      simp
  have hfker : ∀ i, (f i).ker ≤ center (U i) := by
    intro i u hu
    have hu1 : ψ (u : K) i = 1 := hu
    have hmem : ψ (u : K) ∈ coordSubgroup T i := u.2
    have h1 : ψ (u : K) = 1 := by
      rw [eq_mulSingle_of_mem_coordSubgroup hmem, hu1]
      simp
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hcen _ h1) (g : K))
  have hTq : ∀ i, IsQuasisimple (T i) := fun i => (isQuasisimple_of_isSimpleGroup (hnonab i)).1
  have hTcenter : ∀ i, center (T i) = ⊥ := fun i => (isQuasisimple_of_isSimpleGroup (hnonab i)).2
  have hqs : ∀ i, IsQuasisimple (commutator ↥(U i)) := fun i =>
    quasisimple_central_extension_derived_of_surjective (f i) (hfsurj i) (hfker i) (hTq i)
  have hder : ∀ i, Group.IsPerfect (commutator ↥(U i)) ∧
      Function.Surjective ((f i).comp (commutator ↥(U i)).subtype) := fun i =>
    let h := central_extension_derived_of_surjective (f i) (hfsurj i) (hfker i) (hTq i).1
    ⟨h.2.1, h.2.2⟩
  let L : I → Subgroup J := fun i => (⁅U i, U i⁆ : Subgroup K).map K.subtype
  have hLiso : ∀ i, ↥(commutator ↥(U i)) ≃* ↥(L i) := fun i =>
    ((commutator ↥(U i)).equivMapOfInjective (U i).subtype (U i).subtype_injective).trans
      ((MulEquiv.subgroupCongr (map_subtype_commutator (U i))).trans
        ((⁅U i, U i⁆ : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective))
  have hcomp : ∀ i, IsComponent (L i) := by
    intro i
    refine ⟨isQuasisimple_of_mulEquiv (hLiso i) (hqs i), ?_⟩
    have := hUn i
    refine Subgroup.IsSubnormal.step (L i) K (Subgroup.map_subtype_le _)
      (Subgroup.Normal.isSubnormal inferInstance) ?_
    change ((⁅U i, U i⁆ : Subgroup K).map K.subtype).comap K.subtype |>.Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  have hcard : ∀ i, Nat.card (L i ⧸ center (L i)) = Nat.card (T i) := by
    intro i
    set f' : ↥(commutator ↥(U i)) →* T i := (f i).comp (commutator ↥(U i)).subtype with hf'
    have hker' : f'.ker ≤ center (commutator ↥(U i)) := by
      intro c hc
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp (hfker i hc) (g : U i))
    have hcenter := comap_center_eq_of_perfect (hder i).1 f' (hder i).2 hker'
    rw [hTcenter i, MonoidHom.comap_bot] at hcenter
    have e1 : ↥(commutator ↥(U i)) ⧸ center (commutator ↥(U i)) ≃* L i ⧸ center (L i) :=
      QuotientGroup.congr _ _ (hLiso i) (Subgroup.map_center_eq (hLiso i))
    have e2 : ↥(commutator ↥(U i)) ⧸ center (commutator ↥(U i)) ≃* T i :=
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f' (hder i).2)
    exact (Nat.card_congr e1.toEquiv).symm.trans (Nat.card_congr e2.toEquiv)
  have hinj : Function.Injective L := by
    intro i j hij
    by_contra hne
    have hLk : (⁅U i, U i⁆ : Subgroup K) = ⁅U j, U j⁆ :=
      Subgroup.map_injective K.subtype_injective hij
    obtain ⟨t, ht⟩ := exists_ne (1 : T i)
    obtain ⟨c, hc⟩ := (hder i).2 t
    have hcK : ((c : ↥(U i)) : K) ∈ (⁅U i, U i⁆ : Subgroup K) := by
      rw [← map_subtype_commutator]
      exact ⟨c, c.2, rfl⟩
    have := hUn j
    have hcj : ((c : ↥(U i)) : K) ∈ U j := Subgroup.commutator_le_left _ _ (hLk ▸ hcK)
    have h1 : ψ ((c : ↥(U i)) : K) i = t := hc
    have h2 := eq_mulSingle_of_mem_coordSubgroup ((hUmem j _).mp hcj)
    rw [h2] at h1
    simp [Pi.mulSingle_eq_of_ne hne] at h1
    exact ht h1.symm
  have horbit : ∀ i j : I, ∃ n : ℕ, (L i).map (MulAut.conj (x ^ n)).toMonoidHom = L j := by
    intro i j
    obtain ⟨n, hn⟩ := htrans i j
    refine ⟨n, ?_⟩
    set β : MulAut K := MulAut.conjNormal (x ^ n) with hβ
    have hUβ : (U i).map β.toMonoidHom = U j := by
      ext k
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hn u).mp hu
      · intro hk
        refine ⟨β.symm k, ?_, β.apply_symm_apply k⟩
        have h1 : ψ (β (β.symm k)) ∈ coordSubgroup T j := by
          rw [β.apply_symm_apply]
          exact hk
        exact (hn (β.symm k)).mpr h1
    have hLβ : (⁅U i, U i⁆ : Subgroup K).map β.toMonoidHom = ⁅U j, U j⁆ := by
      rw [Subgroup.map_commutator, hUβ]
    change ((⁅U i, U i⁆ : Subgroup K).map K.subtype).map (MulAut.conj (x ^ n)).toMonoidHom =
      (⁅U j, U j⁆ : Subgroup K).map K.subtype
    rw [Subgroup.map_map, ← hLβ, Subgroup.map_map]
    congr 1
  exact ⟨L, hcomp, hcard, hinj, horbit⟩

theorem false_of_semisimple_component_orbit {J : Type} [Group J] [Finite J] {m : ℕ}
    (he : CFSG.Assembly.evenRank J ≤ m) {p : ℕ} (hp : p.Prime) {x : J}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) (K : Subgroup J) [K.Normal] (hKperf : ⁅K, K⁆ = K)
    (C : Subgroup J) [C.Normal] (hCK : C ≤ K) (hCnil : Group.IsNilpotent C)
    (hCodd : Odd (Nat.card C)) {I : Type} [Fintype I] [DecidableEq I]
    (hI : m + 2 ≤ Fintype.card I) (T : I → Type) [∀ i, Group (T i)] [∀ i, Finite (T i)]
    [∀ i, IsSimpleGroup (T i)] (hnonab : ∀ i, ∃ a b : T i, a * b ≠ b * a)
    (heven : ∀ i, Even (Nat.card (T i))) (ψ : K →* ∀ i, T i) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = C.subgroupOf K)
    (htrans : ∀ i j : I, ∃ n : ℕ, ∀ k : K,
      ψ k ∈ coordSubgroup T i ↔ ψ (MulAut.conjNormal (x ^ n) k) ∈ coordSubgroup T j) :
    False := by
  classical
  have hKperf' : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKperf
  let act : MulDistribMulAction J K :=
    MulDistribMulAction.compHom K (MulAut.conjNormal : J →* MulAut K)
  have hsmul : ∀ (g : J) (k : K), g • k = MulAut.conjNormal g k := fun _ _ => rfl
  have hCinv : ∀ (a : J) (c : K), c ∈ C.subgroupOf K → a • c ∈ C.subgroupOf K := by
    intro a c hc
    rw [hsmul, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact Subgroup.Normal.conj_mem ‹C.Normal› _ hc a
  have hnil' : Group.IsNilpotent (C.subgroupOf K) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCK).symm
  have hodd' : Odd (Nat.card (C.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv]
  let φ : K ⧸ C.subgroupOf K ≃* ∀ i, T i :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hcen : C.subgroupOf K ≤ center K :=
    transitive_semisimple_odd_kernel_centralization m K hKperf'
      ((Sec9A.evenRank_subgroup_le K).trans he) J (C.subgroupOf K) hCinv hnil' hodd' I hI T
      hnonab heven φ (fun i j => by
        obtain ⟨n, hn⟩ := htrans i j
        exact ⟨x ^ n, fun k => hn k⟩)
  have hcen' : ∀ k : K, ψ k = 1 → k ∈ center K := fun k hk =>
    hcen (by rw [← hker]; exact hk)
  obtain ⟨L, hcomp, hcard, hinj, horbit⟩ :=
    exists_component_family K T hnonab ψ hψ hcen' x htrans
  have hIpos : 0 < Fintype.card I := by omega
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hIpos
  obtain ⟨q, hq, hq2, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card (T i₀) := by
    by_contra hno
    have hpow : ∃ k : ℕ, Nat.card (T i₀) = 2 ^ k :=
      ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd => by
        by_contra hr2
        exact hno ⟨r, hr, hr2, hrd⟩)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2grp : IsPGroup 2 (T i₀) := by
      obtain ⟨k, hk⟩ := hpow
      exact IsPGroup.of_card (n := k) hk
    have := h2grp.isNilpotent
    obtain ⟨a, b, hab⟩ := hnonab i₀
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  have h2q : 2 * q ∣ Nat.card (L i₀ ⧸ center (L i₀)) := by
    rw [hcard]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm)
      (even_iff_two_dvd.mp (heven i₀)) hqdvd
  set O := Set.range fun n : ℤ => (L i₀).map (MulAut.conj (x ^ n)).toMonoidHom with hO
  have hsub : Set.range L ⊆ O := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨n, hn⟩ := horbit i₀ j
    exact ⟨(n : ℤ), by simpa only [zpow_natCast] using hn⟩
  have hcardO : Fintype.card I ≤ O.ncard := by
    calc Fintype.card I = (Set.range L).ncard := by
          rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
            Nat.card_eq_fintype_card]
      _ ≤ O.ncard := Set.ncard_le_ncard hsub (Set.toFinite O)
  have hmove : (L i₀).map (MulAut.conj x).toMonoidHom ≠ L i₀ := by
    intro h
    have hxn : x ∈ normalizer (L i₀ : Set J) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    have hO1 : O ⊆ {L i₀} := by
      rintro _ ⟨n, rfl⟩
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp ((normalizer (L i₀ : Set J)).zpow_mem hxn n)
    have := Set.ncard_le_ncard hO1 (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨-, -, u, -, V, -, -, -, hV, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.component_orbit_ambient_local_rank_witness hp hx
      (hcomp i₀) hmove hq h2q (d := O.ncard) rfl
  have hle := (CFSG.RankThree.OddKernel.localRank_le_evenRank hq hq2).trans he
  omega

theorem false_of_semisimple_cover_image {J Ĵ : Type} [Group J] [Group Ĵ] [Finite J] [Finite Ĵ]
    (q : J →* Ĵ) (hq : Function.Surjective q) {m : ℕ} (he : CFSG.Assembly.evenRank Ĵ ≤ m)
    {p : ℕ} (hp : p.Prime) {x : J} (hx : ∃ k : ℕ, orderOf x = p ^ k) (K : Subgroup J)
    [K.Normal] (hKperf : ⁅K, K⁆ = K) (C : Subgroup J) [C.Normal] (hCK : C ≤ K)
    (hCnil : Group.IsNilpotent C) (hCodd : Odd (Nat.card (C.map q)))
    (hqK : ∀ k ∈ K, q k = 1 → k ∈ C) {I : Type} [Fintype I] [DecidableEq I]
    (hI : m + 2 ≤ Fintype.card I) (T : I → Type) [∀ i, Group (T i)] [∀ i, Finite (T i)]
    [∀ i, IsSimpleGroup (T i)] (hnonab : ∀ i, ∃ a b : T i, a * b ≠ b * a)
    (heven : ∀ i, Even (Nat.card (T i))) (ψ : K →* ∀ i, T i) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = C.subgroupOf K)
    (htrans : ∀ i j : I, ∃ n : ℕ, ∀ k : K,
      ψ k ∈ coordSubgroup T i ↔ ψ (MulAut.conjNormal (x ^ n) k) ∈ coordSubgroup T j) :
    False := by
  classical
  have hKn : (K.map q).Normal := Subgroup.Normal.map ‹K.Normal› q hq
  have hCn : (C.map q).Normal := Subgroup.Normal.map ‹C.Normal› q hq
  let f : K →* K.map q := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hfapp : ∀ k : K, ((f k : K.map q) : Ĵ) = q k := fun k => rfl
  have hle : f.ker ≤ ψ.ker := by
    intro k hk
    have h1 : q (k : J) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      exact this
    rw [hker, Subgroup.mem_subgroupOf]
    exact hqK k k.2 h1
  let ψ' : K.map q →* ∀ i, T i := f.liftOfSurjective hf ⟨ψ, hle⟩
  have hψ' : ∀ k : K, ψ' (f k) = ψ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨ψ, hle⟩ k
  have hψ's : Function.Surjective ψ' := by
    intro s
    obtain ⟨k, hk⟩ := hψ s
    exact ⟨f k, by rw [hψ', hk]⟩
  have hker' : ψ'.ker = (C.map q).subgroupOf (K.map q) := by
    ext k'
    obtain ⟨k, rfl⟩ := hf k'
    rw [MonoidHom.mem_ker, hψ', ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, hfapp]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨c, hc, hck⟩
      have h1 : q (c⁻¹ * (k : J)) = 1 := by rw [map_mul, map_inv, hck, inv_mul_cancel]
      have h2 : c⁻¹ * (k : J) ∈ C := hqK _ (K.mul_mem (K.inv_mem (hCK hc)) k.2) h1
      have h3 := C.mul_mem hc h2
      rwa [mul_inv_cancel_left] at h3
  have hxq : ∃ k : ℕ, orderOf (q x) = p ^ k := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ orderOf_map_dvd q x)
    exact ⟨j, hj⟩
  refine false_of_semisimple_component_orbit he hp hxq (K.map q) ?_ (C.map q)
    (Subgroup.map_mono hCK)
    (Group.nilpotent_of_surjective (q.subgroupMap C) (q.subgroupMap_surjective C)) hCodd hI T
    hnonab heven ψ' hψ's hker' ?_
  · rw [← Subgroup.map_commutator, hKperf]
  · intro i j
    obtain ⟨n, hn⟩ := htrans i j
    refine ⟨n, fun k' => ?_⟩
    obtain ⟨k, rfl⟩ := hf k'
    have hconj : MulAut.conjNormal (q x ^ n) (f k) = f (MulAut.conjNormal (x ^ n) k) := by
      apply Subtype.ext
      change (q x ^ n) * q k * (q x ^ n)⁻¹ = q ((x ^ n) * k * (x ^ n)⁻¹)
      rw [map_mul, map_mul, map_inv, map_pow]
    rw [hconj, hψ', hψ']
    exact hn k

theorem evenRank_quotient_le {G : Type} [Group G] [Finite G] {m : ℕ}
    (he : CFSG.Assembly.evenRank G ≤ m) (P J : Subgroup G) (hPJ : P ≤ J)
    (hJ : J ≤ normalizer (P : Set G)) (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    [(P.subgroupOf J).Normal] : CFSG.Assembly.evenRank (J ⧸ P.subgroupOf J) ≤ m := by
  have hloc : CFSG.Open.IsTwoLocal (normalizer (P : Set G)) := ⟨P, hP1, hP2, rfl⟩
  have hJrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r J ≤ m := by
    intro r hr hr2
    calc CFSG.pRank r J = CFSG.Open.pRank r (⊤ : Subgroup J) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top r J
      _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup J).map J.subtype) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt J.subtype J.subtype_injective ⊤
      _ ≤ CFSG.Open.pRank r (normalizer (P : Set G)) :=
          CFSG.SectionRank.pRank_mono hr.one_lt (by
            rintro _ ⟨j, -, rfl⟩
            exact hJ j.2)
      _ ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 _ hloc
      _ = CFSG.Assembly.evenRank G := rfl
      _ ≤ m := he
  refine CFSG.RankThree.Coprime.evenRank_le_of_pRank_le fun r hr hr2 => ?_
  have hrP : ¬ r ∣ Nat.card (P.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv]
    intro hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr (P.subgroupOf J) hrP]
  exact hJrank r hr hr2

theorem exists_induced_mulAut {H S : Type*} [Group H] [Group S] [Finite S] (π : H →* S)
    (hπ : Function.Surjective π) (α : MulAut H) (hα : ∀ h : H, π h = 1 → π (α h) = 1) :
    ∃ σ : MulAut S, ∀ h : H, σ (π h) = π (α h) := by
  have hle : π.ker ≤ (π.comp α.toMonoidHom).ker := fun h hh => hα h hh
  let σ₀ : S →* S := π.liftOfSurjective hπ ⟨π.comp α.toMonoidHom, hle⟩
  have hσ₀ : ∀ h : H, σ₀ (π h) = π (α h) := fun h =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨π.comp α.toMonoidHom, hle⟩ h
  have hsurj : Function.Surjective σ₀ := by
    intro s
    obtain ⟨h, rfl⟩ := hπ s
    exact ⟨π (α.symm h), by rw [hσ₀, α.apply_symm_apply]⟩
  exact ⟨MulEquiv.ofBijective σ₀ ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩, hσ₀⟩

theorem exists_invariant_minimal_cover {H S : Type*} [Group H] [Finite H] [Group S] [Finite S]
    {p k : ℕ} (hp : p.Prime) (hpH : ¬ p ∣ Nat.card H) (hSperf : Group.IsPerfect S)
    (π : H →* S) (hπ : Function.Surjective π) (α : MulAut H) (hαpow : α ^ (p ^ k) = 1)
    (hker : ∀ h : H, π h = 1 → π (α h) = 1) :
    ∃ K : Subgroup H, K.map π = ⊤ ∧ ⁅K, K⁆ = K ∧ K.map α.toMonoidHom = K ∧
      Group.IsNilpotent ↥(K ⊓ π.ker) ∧ ((K ⊓ π.ker).subgroupOf K).Normal ∧
      (K ⊓ π.ker).map α.toMonoidHom = K ⊓ π.ker ∧
      ∀ R : Sylow 2 ↥(K ⊓ π.ker),
        (((R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype).subgroupOf K).Normal ∧
        ((R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype).map α.toMonoidHom =
          (R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype := by
  classical
  obtain ⟨σ, hσ⟩ := exists_induced_mulAut π hπ α hker
  have hσn : ∀ (n : ℕ) (h : H), (σ ^ n) (π h) = π ((α ^ n) h) := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      rw [pow_succ, MulAut.mul_apply, hσ, ih, pow_succ, MulAut.mul_apply]
  have hσpow : σ ^ (p ^ k) = 1 := by
    ext s
    obtain ⟨h, rfl⟩ := hπ s
    rw [hσn, hαpow]
    rfl
  set g : MulAut H × MulAut S := (α, σ) with hg
  have hgpow : g ^ (p ^ k) = 1 := Prod.ext hαpow hσpow
  have hApg : IsPGroup p (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hgpow)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  let _ : MulDistribMulAction (Subgroup.zpowers g) H :=
    MulDistribMulAction.compHom H
      ((MonoidHom.fst (MulAut H) (MulAut S)).comp (Subgroup.zpowers g).subtype)
  let _ : MulDistribMulAction (Subgroup.zpowers g) S :=
    MulDistribMulAction.compHom S
      ((MonoidHom.snd (MulAut H) (MulAut S)).comp (Subgroup.zpowers g).subtype)
  have hπA : ∀ (a : Subgroup.zpowers g) (h : H), π (a • h) = a • π h := by
    rintro ⟨a, ha⟩ h
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ha)
    exact (hσn n h).symm
  obtain ⟨K, hKinv, hKS, hKmin⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.exists_minimal_invariant_cover
      (A := Subgroup.zpowers g) π hπ
  obtain ⟨hKperf, hCinv, hCn, hCnil, hSyl⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.coprime_invariant_minimal_perfect_cover
      (A := Subgroup.zpowers g) hp hApg π hπA hpH hSperf K hKinv hKS hKmin
  have hinv : ∀ X : Subgroup H, (∀ a : Subgroup.zpowers g, ∀ y ∈ X, a • y ∈ X) →
      X.map α.toMonoidHom = X := by
    intro X hX
    have hle : X.map α.toMonoidHom ≤ X := by
      rintro _ ⟨y, hy, rfl⟩
      exact hX ⟨g, Subgroup.mem_zpowers g⟩ y hy
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective α.injective])
  refine ⟨K, hKS, hKperf, hinv K hKinv, hCnil, hCn, hinv _ hCinv, fun R => ?_⟩
  by_cases hd : 2 ∣ Nat.card (K ⊓ π.ker : Subgroup H)
  · obtain ⟨-, hPn, hPinv⟩ := hSyl 2 Nat.prime_two hd R
    exact ⟨hPn, hinv _ hPinv⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR : (R : Subgroup ↥(K ⊓ π.ker)) = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [R.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    rw [hR, Subgroup.map_bot]
    exact ⟨by rw [Subgroup.bot_subgroupOf]; infer_instance, Subgroup.map_bot _⟩

theorem odd_natCard_quotient {Y C : Type*} [Group Y] [Finite Y] [Group C] [Finite C]
    (R : Sylow 2 C) (s : Subgroup Y) (hY : Nat.card Y = Nat.card C)
    (hs : Nat.card s = Nat.card (R : Subgroup C)) : Odd (Nat.card (Y ⧸ s)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup s
  have h2 := ((R : Subgroup C).card_mul_index).symm
  have hpos : 0 < Nat.card (R : Subgroup C) := Nat.card_pos
  have h3 : Nat.card (Y ⧸ s) * Nat.card (R : Subgroup C) = (R : Subgroup C).index *
      Nat.card (R : Subgroup C) :=
    calc Nat.card (Y ⧸ s) * Nat.card (R : Subgroup C) = Nat.card (Y ⧸ s) * Nat.card s := by
          rw [hs]
      _ = Nat.card Y := h1.symm
      _ = Nat.card C := hY
      _ = Nat.card (R : Subgroup C) * (R : Subgroup C).index := h2
      _ = _ := mul_comm _ _
  have h4 := Nat.eq_of_mul_eq_mul_right hpos h3
  rw [h4]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp R.not_dvd_index)

theorem false_of_cover_data {G : Type} [Group G] [Finite G] {m : ℕ}
    (he : CFSG.Assembly.evenRank G ≤ m) {p : ℕ} (hp : p.Prime) {x : G} {k₀ : ℕ}
    (hk₀ : orderOf x = p ^ k₀) {H : Subgroup G} (α : MulAut H)
    (hα : ∀ (n : ℕ) (h : H), (((α ^ n) h : H) : G) = x ^ n * (h : G) * (x ^ n)⁻¹)
    {I : Type} [Fintype I] [DecidableEq I] (hI : m + 2 ≤ Fintype.card I)
    (T : I → Type) [∀ i, Group (T i)] [∀ i, Finite (T i)] [∀ i, IsSimpleGroup (T i)]
    (hnonab : ∀ i, ∃ a b : T i, a * b ≠ b * a) (heven : ∀ i, Even (Nat.card (T i)))
    (π : H →* ∀ i, T i)
    (htrans : ∀ i j : I, ∃ n : ℕ, ∀ h : H,
      π h ∈ coordSubgroup T i ↔ π ((α ^ n) h) ∈ coordSubgroup T j)
    (K : Subgroup H) (R : Sylow 2 ↥(K ⊓ π.ker)) (hKS : K.map π = ⊤) (hKperf : ⁅K, K⁆ = K)
    (hKα : K.map α.toMonoidHom = K) (hCnil : Group.IsNilpotent ↥(K ⊓ π.ker))
    (hCn : ((K ⊓ π.ker).subgroupOf K).Normal)
    (hCα : (K ⊓ π.ker).map α.toMonoidHom = K ⊓ π.ker)
    (hPn : (((R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype).subgroupOf K).Normal)
    (hPα : ((R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype).map α.toMonoidHom =
      (R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype) : False := by
  classical
  have hpoint : ∀ X : Subgroup H, X.map α.toMonoidHom = X → ∀ h ∈ X, α h ∈ X := by
    intro X hX h hh
    have : α h ∈ X.map α.toMonoidHom := ⟨h, hh, rfl⟩
    rwa [hX] at this
  have hαn : ∀ X : Subgroup H, X.map α.toMonoidHom = X → ∀ (n : ℕ) (h : H), h ∈ X →
      (α ^ n) h ∈ X := by
    intro X hX n
    induction n with
    | zero => intro h hh; simpa using hh
    | succ n ih =>
      intro h hh
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hpoint X hX h hh)
  have hconj : ∀ X : Subgroup H, X.map α.toMonoidHom = X →
      x ∈ normalizer ((X.map H.subtype : Subgroup G) : Set G) := by
    intro X hX
    have hcomp : (MulAut.conj x).toMonoidHom.comp H.subtype = H.subtype.comp α.toMonoidHom := by
      ext h
      simpa using (hα 1 h).symm
    have hmap : (X.map H.subtype).map (MulAut.conj x).toMonoidHom = X.map H.subtype := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hX]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  set P : Subgroup H := (R : Subgroup ↥(K ⊓ π.ker)).map (K ⊓ π.ker).subtype with hP
  have hPC : P ≤ K ⊓ π.ker := Subgroup.map_subtype_le _
  have hCK : K ⊓ π.ker ≤ K := inf_le_left
  have hP2 : IsPGroup 2 P := R.isPGroup'.map _
  set KG : Subgroup G := K.map H.subtype with hKG
  set CG : Subgroup G := (K ⊓ π.ker).map H.subtype with hCG
  set PG : Subgroup G := P.map H.subtype with hPG
  have hCGK : CG ≤ KG := Subgroup.map_mono hCK
  have hPGC : PG ≤ CG := Subgroup.map_mono hPC
  have hxK : x ∈ normalizer (KG : Set G) := hconj K hKα
  have hxC : x ∈ normalizer (CG : Set G) := hconj (K ⊓ π.ker) hCα
  have hxP : x ∈ normalizer (PG : Set G) := hconj P hPα
  have hKnC : KG ≤ normalizer (CG : Set G) :=
    (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mp hCn)).trans
      (Subgroup.le_normalizer_map _)
  have hKnP : KG ≤ normalizer (PG : Set G) :=
    (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer (hPC.trans hCK)).mp
      hPn)).trans (Subgroup.le_normalizer_map _)
  set JG : Subgroup G := KG ⊔ Subgroup.zpowers x with hJG
  have hxJ : x ∈ JG := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hKJ : KG ≤ JG := le_sup_left
  have hJK : JG ≤ normalizer (KG : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxK)
  have hJC : JG ≤ normalizer (CG : Set G) := sup_le hKnC (Subgroup.zpowers_le.mpr hxC)
  have hJP : JG ≤ normalizer (PG : Set G) := sup_le hKnP (Subgroup.zpowers_le.mpr hxP)
  have hK₀n : (KG.subgroupOf JG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK
  have hC₀n : (CG.subgroupOf JG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hCGK.trans hKJ)).mpr hJC
  let eK : ↥K ≃* ↥(KG.subgroupOf JG) :=
    (K.equivMapOfInjective H.subtype H.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hKJ).symm
  have heK : ∀ k : K, (((eK k : ↥(KG.subgroupOf JG)) : ↥JG) : G) = ((k : H) : G) :=
    fun k => rfl
  let ψ : ↥(KG.subgroupOf JG) →* ∀ i, T i := (π.comp K.subtype).comp eK.symm.toMonoidHom
  have hψ : ∀ k : K, ψ (eK k) = π (k : H) := fun k => by simp [ψ]
  have hψs : Function.Surjective ψ := by
    intro s
    have hs : s ∈ K.map π := by
      rw [hKS]
      exact Subgroup.mem_top s
    obtain ⟨k, hk, hks⟩ := hs
    exact ⟨eK ⟨k, hk⟩, by rw [hψ]; exact hks⟩
  have hker' : ψ.ker = (CG.subgroupOf JG).subgroupOf (KG.subgroupOf JG) := by
    ext k₀
    obtain ⟨k, rfl⟩ := eK.surjective k₀
    have hmem : ((k : H) : G) ∈ CG ↔ (k : H) ∈ K ⊓ π.ker :=
      Subgroup.mem_map_iff_mem H.subtype_injective
    rw [MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, heK, hmem]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hαK : ∀ (n : ℕ) (k : K), (α ^ n) (k : H) ∈ K := fun n k => hαn K hKα n k k.2
  have hconjeK : ∀ (n : ℕ) (k : K), MulAut.conjNormal ((⟨x, hxJ⟩ : ↥JG) ^ n) (eK k) =
      eK ⟨(α ^ n) (k : H), hαK n k⟩ := by
    intro n k
    refine Subtype.ext (Subtype.ext ?_)
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      heK]
    exact (hα n k).symm
  have htrans' : ∀ i j : I, ∃ n : ℕ, ∀ k₀ : ↥(KG.subgroupOf JG),
      ψ k₀ ∈ coordSubgroup T i ↔
        ψ (MulAut.conjNormal ((⟨x, hxJ⟩ : ↥JG) ^ n) k₀) ∈ coordSubgroup T j := by
    intro i j
    obtain ⟨n, hn⟩ := htrans i j
    refine ⟨n, fun k₀ => ?_⟩
    obtain ⟨k, rfl⟩ := eK.surjective k₀
    rw [hconjeK, hψ, hψ]
    exact hn k
  have hKperf' : ⁅KG.subgroupOf JG, KG.subgroupOf JG⁆ = KG.subgroupOf JG := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥(KG.subgroupOf JG) :=
      Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hCnil' : Group.IsNilpotent ↥(CG.subgroupOf JG) :=
    Group.nilpotent_of_mulEquiv
      (((K ⊓ π.ker).equivMapOfInjective H.subtype H.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe (hCGK.trans hKJ)).symm)
  have hxJ' : ∃ k : ℕ, orderOf (⟨x, hxJ⟩ : ↥JG) = p ^ k :=
    ⟨k₀, by rw [← hk₀, ← Subgroup.orderOf_coe]⟩
  have key : ∀ (Ĵ : Type) [Group Ĵ] [Finite Ĵ] (q : ↥JG →* Ĵ), Function.Surjective q →
      CFSG.Assembly.evenRank Ĵ ≤ m →
      (∀ k ∈ KG.subgroupOf JG, q k = 1 → k ∈ CG.subgroupOf JG) →
      Odd (Nat.card ((CG.subgroupOf JG).map q)) → False := by
    intro Ĵ _ _ q hq hê hqK hodd
    exact false_of_semisimple_cover_image q hq hê hp hxJ' (KG.subgroupOf JG) hKperf'
      (CG.subgroupOf JG) (fun k hk => hCGK hk) hCnil' hodd hqK hI T hnonab heven ψ hψs hker'
      htrans'
  have hY : Nat.card ↥(CG.subgroupOf JG) = Nat.card ↥(K ⊓ π.ker) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hCGK.trans hKJ)).toEquiv).trans
      (Subgroup.card_map_of_injective H.subtype_injective)
  by_cases hPbot : P = ⊥
  ·
    have hRbot : (R : Subgroup ↥(K ⊓ π.ker)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (K ⊓ π.ker).subtype_injective).mp hPbot
    refine key ↥JG (MonoidHom.id ↥JG) Function.surjective_id
      ((Sec9A.evenRank_subgroup_le JG).trans he) (fun k _ hk => ?_) ?_
    · have hk1 : k = 1 := hk
      rw [hk1]
      exact one_mem _
    · rw [Subgroup.map_id]
      have h := odd_natCard_quotient R (⊥ : Subgroup ↥(CG.subgroupOf JG)) hY
        (by rw [Subgroup.card_bot, hRbot, Subgroup.card_bot])
      rwa [Nat.card_congr QuotientGroup.quotientBot.toEquiv] at h
  ·
    have hPG1 : PG ≠ ⊥ := fun h =>
      hPbot ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
    have hP₀n : (PG.subgroupOf JG).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hPGC.trans (hCGK.trans hKJ))).mpr hJP
    have hPJ : PG.subgroupOf JG ≤ CG.subgroupOf JG := fun k hk => hPGC hk
    refine key (↥JG ⧸ PG.subgroupOf JG) (QuotientGroup.mk' (PG.subgroupOf JG))
      (QuotientGroup.mk'_surjective _)
      (evenRank_quotient_le he PG JG (hPGC.trans (hCGK.trans hKJ)) hJP (hP2.map _) hPG1)
      (fun k _ hk => hPJ ((QuotientGroup.eq_one_iff k).mp hk)) ?_
    rw [CFSG.natCard_map_mk'_eq]
    refine odd_natCard_quotient R ((PG.subgroupOf JG).subgroupOf (CG.subgroupOf JG)) hY ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPGC.trans (hCGK.trans hKJ))).toEquiv,
      hPG, Subgroup.card_map_of_injective H.subtype_injective,
      hP, Subgroup.card_map_of_injective (K ⊓ π.ker).subtype_injective]

end CoprimeSemisimpleOrbit

open CoprimeSemisimpleOrbit

theorem coprime_transitive_semisimple_section_orbit_bound :
    CoprimeTransitiveSemisimpleSectionOrbitBound := by
  intro G _ _ m he p hp hp2 x hxk H hx hpH I _ _ _ T _ _ _ hnonab heven π hπ hker htrans
  classical
  by_contra hlt
  have hI : m + 2 ≤ Fintype.card I := by omega
  obtain ⟨k₀, hk₀⟩ := hxk
  set α : MulAut H := H.normalizerMonoidHom ⟨x, hx⟩ with hα
  have hαapp : ∀ (n : ℕ) (h : H), (((α ^ n) h : H) : G) = x ^ n * (h : G) * (x ^ n)⁻¹ := by
    intro n h
    rw [hα, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow]
  have hαpow : α ^ (p ^ k₀) = 1 := by
    rw [hα, ← map_pow]
    have : (⟨x, hx⟩ : normalizer (H : Set G)) ^ (p ^ k₀) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hk₀]; exact pow_orderOf_eq_one x)
    rw [this, map_one]
  have hTperf : ∀ i, Group.IsPerfect (T i) := fun i =>
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hnonab i)).1.1
  have hSperf : Group.IsPerfect (∀ i, T i) := by
    rw [Group.isPerfect_def]
    refine eq_top_iff.mpr fun y _ => Subgroup.pi_mem_of_mulSingle_mem y fun i => ?_
    have h1 : (commutator (T i)).map (MonoidHom.mulSingle T i) ≤ commutator (∀ i, T i) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rw [(hTperf i).commutator_eq_top, Subgroup.map_top] at h1
    exact h1 ⟨y i, rfl⟩
  obtain ⟨K, hKS, hKperf, hKα, hCnil, hCn, hCα, hSyl⟩ :=
    exists_invariant_minimal_cover hp hpH hSperf π hπ α hαpow hker
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(K ⊓ π.ker)) := inferInstance
  obtain ⟨hPn, hPα⟩ := hSyl R
  exact false_of_cover_data he hp hk₀ α hαapp hI T hnonab heven π htrans K R hKS hKperf hKα hCnil
    hCn hCα hPn hPα

end CFSG.RankThree.PartOne
