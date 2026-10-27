module

public import CFSG.Quasithin.H13.A5S136ab2
public import CFSG.Quasithin.H13.A5S136abP

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace ConfAB

theorem conj_range_normal (X : Type*) [Group X] : (MulAut.conj : X →* MulAut X).range.Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ φ
  refine ⟨φ g, ?_⟩
  ext x
  show φ g * x * (φ g)⁻¹ = φ (g * φ⁻¹ x * g⁻¹)
  rw [map_mul, map_mul, map_inv]
  congr 2
  exact (MulEquiv.apply_symm_apply φ x).symm

theorem mem_range_conj_of_inv {X : Type*} [Group X] {α β γ : MulAut X} (hβ : β ^ 3 = 1)
    {k : ℕ} (hγ : γ ^ 2 ^ k = 1) (hinv : α * β * α⁻¹ = γ * β⁻¹)
    (hc : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  have := conj_range_normal X
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have h1 : (QuotientGroup.mk (α * β * α⁻¹ * β⁻¹) : MulAut X ⧸ I) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [hinv, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  have h3 : (QuotientGroup.mk γ : MulAut X ⧸ I) = (QuotientGroup.mk β) ^ 2 := by
    calc (QuotientGroup.mk γ : MulAut X ⧸ I)
        = (QuotientGroup.mk γ * (QuotientGroup.mk β)⁻¹ * (QuotientGroup.mk β)⁻¹) *
          (QuotientGroup.mk β) ^ 2 := by group
      _ = (QuotientGroup.mk β) ^ 2 := by rw [h1, one_mul]
  have h4 : (QuotientGroup.mk β : MulAut X ⧸ I) ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul, ← h3, ← QuotientGroup.mk_pow, hγ, QuotientGroup.mk_one]
  have h5 : (QuotientGroup.mk β : MulAut X ⧸ I) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  exact (QuotientGroup.eq_one_iff _).mp (eq_one_of_pow_two_pow_of_odd h4 h5 (by decide))

theorem indHom_of_mem {G : Type} [Group G] {K : Subgroup G} {X : Type} [Group X]
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) {k : G} (hk : k ∈ K) :
    indHom K ψ ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (ψ ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) := by
  ext x
  obtain ⟨x, rfl⟩ := ψ.surjective x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [indHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

end ConfAB

open ConfAB in
theorem not_conf1366_of_lie_inner (hEven : Ch1.EvenLieAutInner) (hF1 : FactLieZCent)
    {G : Type} [Group G] [Finite G] {K X Q : Subgroup G} {a z l : G}
    (hqs : CFSG.IsQuasisimple ↥K) (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hS : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K))
    (hL : LieZCentList (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlinn : ∀ hlN : l ∈ Subgroup.normalizer (K : Set G), ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K,
      indHom K (MulEquiv.refl _) ⟨l, hlN⟩ = MulAut.conj k) :
    ¬ Conf1366 K X Q a z l := by
  refine not_conf1366_of_zcent hqs (MulEquiv.refl _) (fun x hx => ?_)
    (fun β hβ hP => hEven _ hS β hβ hP) hlinn (hF1 _ hL)
  have hxZ : x ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Subgroup.mem_center_iff.mpr fun g => (hx g).symm
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hxZ

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pow_three_eq_one_of_mem_Lv {y : G} (hy : y ∈ S.Lv) (hodd : Odd (orderOf y)) :
    y ^ 3 = 1 := by
  obtain ⟨hN, hρ⟩ := S.rho_Lv hy
  have h3 : S.frame.ρ (⟨y, hN⟩ ^ 3) = 1 := by
    rw [map_pow]
    rcases hρ with h | h | h <;> rw [h] <;> decide
  have hy3 : ((⟨y, hN⟩ ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.Lv := by
    simpa using S.Lv.pow_mem hy 3
  obtain ⟨k, hk⟩ := S.two_pow_of_Lv_of_rho (⟨y, hN⟩ ^ 3) hy3 h3
  have hk' : (y ^ 3) ^ 2 ^ k = 1 := by simpa using hk
  have hm : (y ^ 3) ^ orderOf y = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  exact ConfAB.eq_one_of_pow_two_pow_of_odd hk' hm hodd

theorem exists_t0 : ∃ t₀ : ↥(Subgroup.normalizer (V : Set G)),
    (t₀ : G) ∈ S.Tv ∧ S.frame.ρ t₀ = pa := by
  obtain ⟨g, hgT, hg⟩ := S.frame.K4_T pa (Or.inr (Or.inl rfl))
  exact ⟨g, ⟨hgT, S.mem_centralizer_v12 g (by rw [hg]; decide +kernel)⟩, hg⟩

theorem two_pow_conj_mul (t₀ : ↥(Subgroup.normalizer (V : Set G))) (ht₀ : (t₀ : G) ∈ S.Tv)
    (hρ : S.frame.ρ t₀ = pa) {x : G} (hx : x ∈ S.Lv) :
    ∃ k : ℕ, ((t₀ : G) * x * (t₀ : G)⁻¹ * x) ^ 2 ^ k = 1 := by
  obtain ⟨hN, hρx⟩ := S.rho_Lv hx
  have hmem : (t₀ : G) * x * (t₀ : G)⁻¹ * x ∈ S.Lv :=
    S.Lv.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv ht₀) x).mp hx) hx
  have hg : S.frame.ρ (t₀ * ⟨x, hN⟩ * t₀⁻¹ * ⟨x, hN⟩) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hρ]
    rcases hρx with h | h | h <;> rw [h] <;> decide
  exact S.two_pow_of_Lv_of_rho _ hmem hg

theorem inner_of_comm_inner {K : Subgroup G} {X : Type} [Group X]
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X)
    (hout : ∀ α β : MulAut X, ∃ g : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj g)
    (hTN : S.Tv ≤ Subgroup.normalizer (K : Set G)) {y : G} (hy : y ∈ S.Lv)
    (hodd : Odd (orderOf y)) (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : X, ConfAB.indHom K ψ ⟨y, hyN⟩ = MulAut.conj k := by
  obtain ⟨t₀, ht₀, hρ⟩ := S.exists_t0
  have ht₀N := hTN ht₀
  obtain ⟨k, hk⟩ := S.two_pow_conj_mul t₀ ht₀ hρ hy
  set n : ↥(Subgroup.normalizer (K : Set G)) := ⟨t₀, ht₀N⟩ with hn
  set m : ↥(Subgroup.normalizer (K : Set G)) := ⟨y, hyN⟩ with hm
  have hβ3 : ConfAB.indHom K ψ m ^ 3 = 1 := by
    have h1 : m ^ 3 = 1 := Subtype.ext (by simpa [hm] using S.pow_three_eq_one_of_mem_Lv hy hodd)
    rw [← map_pow, h1, map_one]
  have hγk : ConfAB.indHom K ψ (n * m * n⁻¹ * m) ^ 2 ^ k = 1 := by
    have h1 : (n * m * n⁻¹ * m) ^ 2 ^ k = 1 := Subtype.ext (by simpa [hn, hm] using hk)
    rw [← map_pow, h1, map_one]
  have hinv : ConfAB.indHom K ψ n * ConfAB.indHom K ψ m * (ConfAB.indHom K ψ n)⁻¹ =
      ConfAB.indHom K ψ (n * m * n⁻¹ * m) * (ConfAB.indHom K ψ m)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv]
    group
  obtain ⟨g, hg⟩ := hout (ConfAB.indHom K ψ n) (ConfAB.indHom K ψ m)
  obtain ⟨k', hk'⟩ := ConfAB.mem_range_conj_of_inv hβ3 hγk hinv ⟨g, hg.symm⟩
  exact ⟨k', hk'.symm⟩

omit S in
theorem conj_le_centralizer_of_ne {H K : Subgroup G} (hK : IsComponentIn K H) {g : G}
    (hg : g ∈ H) (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (K : Set G) := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hKH : K ≤ H := hK.1
  have hKc : K ∈ cComp H := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h2
  have hK'c : K' ∈ cComp H := map_conj_mem_cComp hKc hg
  have hK'H : K' ≤ H := le_of_mem_cComp hK'c
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKH)).1 hK.2.1
  have hqs' : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (K.equivMapOfInjective _ (MulAut.conj g).injective) hqs
  have hc' : CFSG.IsComponent (K'.subgroupOf H) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'H).symm hqs',
      A5.C25.subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hK'c)⟩
  rcases CFSG.LocalCores.distinct_components_commute hK.2 hc' with h | h
  · exfalso
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hKH, ← Subgroup.map_subgroupOf_eq_of_le hK'H, h]
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk)
    have h2 := (Subgroup.mem_centralizer_iff.1 h1) ⟨x, hK'H hx⟩ hx
    exact (congrArg Subtype.val h2).symm

omit S in
theorem inner_of_mem_conjClosure {H K : Subgroup G} (hK : IsComponentIn K H) {X : Type}
    [Group X] (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) {y : G} (hyC : y ∈ conjClosure K H)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : X, ConfAB.indHom K ψ ⟨y, hyN⟩ = MulAut.conj k := by
  set W : Subgroup G := ((MulAut.conj : X →* MulAut X).range.comap
    (ConfAB.indHom K ψ)).map (Subgroup.normalizer (K : Set G)).subtype with hW
  have hle : conjClosure K H ≤ W := by
    refine conjClosure_le fun g hg k hk => ?_
    by_cases heq : K.map (MulAut.conj g).toMonoidHom = K
    · have hmem : g * k * g⁻¹ ∈ K := by
        rw [← heq]
        exact ⟨k, hk, rfl⟩
      refine ⟨⟨_, Subgroup.le_normalizer hmem⟩, ?_, rfl⟩
      exact ⟨_, (ConfAB.indHom_of_mem ψ hmem).symm⟩
    · have hC := conj_le_centralizer_of_ne hK hg heq ⟨k, hk, rfl⟩
      refine ⟨⟨_, Subgroup.centralizer_le_normalizer _ hC⟩, ?_, rfl⟩
      exact ⟨1, by rw [map_one, ConfAB.indHom_eq_one_of_mem_centralizer K ψ hC]⟩
  obtain ⟨⟨y', hy'N⟩, ⟨k, hk⟩, rfl⟩ := hle hyC
  exact ⟨k, hk.symm⟩

theorem inner_of_not_normal (h122 : Vol2Native.Lemma122A) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hnn : ¬ (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).Normal)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) {X : Type} [Group X]
    (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) {y : G} (hy : y ∈ S.Lv) (hodd : Odd (orderOf y))
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : X, ConfAB.indHom K ψ ⟨y, hyN⟩ = MulAut.conj k := by
  have : IsSimpleGroup G := S.h13.simple
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKH : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h2
  have hcore := qtkeCore_of_cat S.h13.nonabelian S.h13.qtke
  have hO2 : CFSG.Open.pCoreOf 2 Gv ≠ ⊥ := S.pCoreOf_Gv_ne_bot'
  rcases Vol2Native.lemma_1_2_1_three hcore.1 h37 h38 hO2 hKc with hn | ⟨h2, -⟩
  · exact absurd hn hnn
  have hcl := h122 G S.h13.simple S.h13.nonabelian hcore Gv K hO2 hKc 3 Nat.prime_three
    (by norm_num) h2 h3
  have hyGv : y ∈ Gv := (oTwoRes_le _ hy).2
  have hyord : ∃ k : ℕ, orderOf y = 3 ^ k := by
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (S.pow_three_eq_one_of_mem_Lv hy hodd)
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hyC : y ∈ conjClosure K Gv := by
    rw [← hcl]
    exact Subgroup.subset_closure ⟨hyGv, hyord⟩
  exact inner_of_mem_conjClosure hK ψ hyC hyN

theorem exists_conf1366_Lv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hinner : Ch1.InducesInner S.z K) :
    ∃ (X Q : Subgroup G) (y : G), y ∈ S.Lv ∧ Conf1366 K X Q S.a S.z y := by
  obtain ⟨X, Q, y₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -, -, -⟩ :=
    S.exists_conf1366 h1222 h517 h37 h38 hK hinner
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨-, -, hzM, -⟩ := (S.lemma115Hyp_Gv h1222 h517).component_action hK
  have hzK : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G) := hzM
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hKc
  obtain ⟨y, hyLv, hyodd, hyz⟩ := S.exists_Lv_odd hKG hLvN hzK
  refine ⟨X, Q, y, hyLv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hLvN hyLv,
    hyodd, ?_, hyz⟩
  rw [S.Lv_comm_a hyLv, mul_inv_cancel]
  exact Subgroup.one_mem _

end Setting

end CFSG.Quasithin.H13.A5
