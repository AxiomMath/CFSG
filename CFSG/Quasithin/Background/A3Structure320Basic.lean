module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

theorem pRank_add_le {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : ¬ p ∣ Nat.card N) {X E : Subgroup G}
    (hX : IsElemAbelian p X) (hE : IsElemAbelian p E)
    (hcomm : ∀ x ∈ X, ∀ e ∈ E, ⁅x, e⁆ ∈ N)
    (hinj : ∀ x ∈ X, ∀ e ∈ E, x * e ∈ N → x = 1 ∧ e = 1)
    {a b : ℕ} (hXa : Nat.card X = p ^ a) (hEb : Nat.card E = p ^ b) :
    a + b ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hcomm' : ∀ (x : X) (e : E), QuotientGroup.mk' N (x : G) * QuotientGroup.mk' N (e : G) =
      QuotientGroup.mk' N (e : G) * QuotientGroup.mk' N (x : G) := by
    intro x e
    have h1 : QuotientGroup.mk' N ⁅(x : G), (e : G)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm x x.2 e e.2)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  let f : ↥X × ↥E →* G ⧸ N :=
    { toFun := fun u => QuotientGroup.mk' N (u.1 : G) * QuotientGroup.mk' N (u.2 : G)
      map_one' := by simp
      map_mul' := by
        intro u v
        have h := hcomm' v.1 u.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
        rw [← mul_assoc (QuotientGroup.mk' N (v.1 : G)), h, mul_assoc] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : QuotientGroup.mk' N ((u.1 : G) * (u.2 : G)) = 1 := by
      simpa [f, map_mul] using hu
    obtain ⟨h2, h3⟩ := hinj u.1 u.1.2 u.2 u.2.2 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hbound : a + b ≤ CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ N)) := by
    have := hX.1
    have := hE.1
    refine le_pRank_of_injective hp.out.one_lt (A := ↥X × ↥E) ?_ ?_ ?_ f hf le_top
    · intro u v
      exact Prod.ext (mul_comm' u.1 v.1) (mul_comm' u.2 v.2)
    · intro u
      exact Prod.ext (Subtype.ext (hX.2 _ u.1.2)) (Subtype.ext (hE.2 _ u.2.2))
    · rw [Nat.card_prod, hXa, hEb, pow_add]
  rwa [pRank_quotient_eq N hN] at hbound

theorem exists_orderOf_eq_three_not_mem {L : Type*} [Group L] [Finite L]
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) {Z : Subgroup L}
    (hZc : Z ≤ Subgroup.center L) (hZ : Nat.card Z = 3) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZ)
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hZP' : Z ≤ (P : Subgroup L) := hZP
  have hnt : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  have hz3 : (z : L) ^ 3 = 1 := by
    have := pow_card_eq_one' (x := z)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hz1 : (z : L) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzc : (z : L) ∈ Subgroup.center L := hZc z.2
  let ϕ : ↥(P : Subgroup L) →* Abelianization ↥(P : Subgroup L) := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * (z : L) ^ k * g₀ ∈ (P : Subgroup L) →
      g₀⁻¹ * (z : L) ^ k * g₀ = (z : L) ^ k := by
    intro k g₀ _
    have h1 := Subgroup.mem_center_iff.1 ((Subgroup.center L).pow_mem hzc k) g₀
    rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzi : (z : L) ^ (P : Subgroup L).index ∈ (P : Subgroup L) :=
    MonoidHom.transfer_eq_pow_aux (z : L) hkey
  have htr := MonoidHom.transfer_eq_pow ϕ (z : L) hkey
  have hT1 : MonoidHom.transfer ϕ (z : L) = 1 := by
    have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
    have hcom : commutator L = ⊤ := by rw [commutator_def]; exact hperf
    exact hle (hcom ▸ Subgroup.mem_top (z : L))
  rw [htr] at hT1
  have hmem : (⟨(z : L) ^ (P : Subgroup L).index, hzi⟩ : ↥(P : Subgroup L)) ∈
      commutator ↥(P : Subgroup L) := by
    rw [← Abelianization.ker_of]
    exact hT1
  let z' : ↥(P : Subgroup L) := ⟨z, hZP' z.2⟩
  have hz'3 : z' ^ 3 = 1 := Subtype.ext hz3
  have hidx : ¬ 3 ∣ (P : Subgroup L).index := P.not_dvd_index
  have hpow : ∀ n : ℕ, z' ^ n = z' ^ (n % 3) := fun n => by
    calc z' ^ n = z' ^ (3 * (n / 3) + n % 3) := by rw [Nat.div_add_mod]
      _ = z' ^ (n % 3) := by rw [pow_add, pow_mul, hz'3, one_pow, one_mul]
  have hz'mem : z' ∈ commutator ↥(P : Subgroup L) := by
    have h1 : z' ^ (P : Subgroup L).index ∈ commutator ↥(P : Subgroup L) := hmem
    have h2 : (P : Subgroup L).index % 3 = 1 ∨ (P : Subgroup L).index % 3 = 2 := by omega
    rw [hpow] at h1
    rcases h2 with h2 | h2
    · rwa [h2, pow_one] at h1
    · rw [h2] at h1
      have h3 : z' = (z' ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hz'3
      rw [h3]
      exact Subgroup.inv_mem _ h1
  have hncyc : ¬ IsCyclic ↥(P : Subgroup L) := by
    intro hcyc
    have hbot : commutator ↥(P : Subgroup L) = ⊥ := by
      rw [commutator_eq_bot_iff]
      infer_instance
    rw [hbot, Subgroup.mem_bot] at hz'mem
    exact hz1 (congrArg Subtype.val hz'mem)
  have : Fact (IsPGroup 3 ↥(P : Subgroup L)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := ↥(P : Subgroup L)) (p := 3)
    (by norm_num) hncyc
  have hZcard' : Nat.card (Z.subgroupOf (P : Subgroup L)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP').toEquiv).trans hZ
  obtain ⟨s, hsS, hsZ⟩ : ∃ s ∈ S, s ∉ Z.subgroupOf (P : Subgroup L) := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ Z.subgroupOf (P : Subgroup L) := hcon
    have := Subgroup.card_le_of_le hle
    rw [hScard, hZcard'] at this
    omega
  have : CFSG.IsElementaryAbelian 3 ↥S := hSel
  have hs3 : s ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian s hsS
  have hsZ' : (s : L) ∉ Z := fun h => hsZ (Subgroup.mem_subgroupOf.2 h)
  refine ⟨(s : L), ?_, hsZ'⟩
  have hs1 : (s : L) ≠ 1 := fun h => hsZ' (h ▸ Z.one_mem)
  exact orderOf_eq_prime (congrArg Subtype.val hs3 : (s : L) ^ 3 = 1) hs1

theorem no_s3_section_of_hom {K K' : Type*} [Group K] [Finite K] [Group K'] (f : K →* K')
    (hfker : ∀ x ∈ f.ker, ¬ 3 ∣ orderOf x) {Z : Subgroup K'} (hZ : Nat.card Z = 3)
    (hcent : ∀ (k : K), ∀ z ∈ Z, f k * z = z * f k)
    (hU : ∀ y : K, orderOf y = 3 → f y ∈ Z)
    (π : K →* Equiv.Perm (Fin 3)) (hπ : Function.Surjective π) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : K →* ℤˣ := Equiv.Perm.sign.comp π with hφdef
  have hφ : Function.Surjective φ := (Equiv.Perm.sign_surjective (Fin 3)).comp hπ
  have hc3 : ∀ c : Equiv.Perm (Fin 3), Equiv.Perm.sign c = 1 → c ^ 3 = 1 := by decide
  have hinv : ∀ c d : Equiv.Perm (Fin 3), Equiv.Perm.sign c = 1 → Equiv.Perm.sign d = -1 →
      d * c * d⁻¹ = c⁻¹ := by decide
  have hker3 : ∀ x : K, (∃ k : ℕ, orderOf x = 3 ^ k) → f x = 1 → x = 1 := by
    rintro x ⟨k, hk⟩ hx
    have h1 := hfker x (MonoidHom.mem_ker.2 hx)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact orderOf_eq_one_iff.1 (by simpa using hk)
    · exact absurd (hk ▸ dvd_pow_self 3 hk0.ne') h1
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 K))
  have hinjP : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), f x = f y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ (P : Subgroup K) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨x⁻¹ * y, hmem⟩
    have h1 : x⁻¹ * y = 1 := hker3 _
      ⟨k, (Subgroup.orderOf_coe (⟨x⁻¹ * y, hmem⟩ : ↥(P : Subgroup K))).trans hk⟩
      (by rw [map_mul, map_inv, hxy, inv_mul_cancel])
    exact (inv_mul_eq_one.1 h1)
  have hcyc : IsCyclic ↥(P : Subgroup K) := by
    by_contra hncyc
    have : Fact (IsPGroup 3 ↥(P : Subgroup K)) := ⟨P.isPGroup'⟩
    obtain ⟨S, -, hScard, hSel⟩ :=
      CFSG.lemma_4_5_a (R := ↥(P : Subgroup K)) (p := 3) (by norm_num) hncyc
    have : CFSG.IsElementaryAbelian 3 ↥S := hSel
    let S' : Subgroup K := S.map (P : Subgroup K).subtype
    have hS'card : Nat.card S' = 9 := by
      rw [Subgroup.card_map_of_injective (P : Subgroup K).subtype_injective, hScard]; norm_num
    have hS'P : S' ≤ (P : Subgroup K) := Subgroup.map_subtype_le S
    have hS'3 : ∀ s ∈ S', s ^ 3 = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      exact congrArg Subtype.val (CFSG.elemPow_eq_one_of_isElementaryAbelian s hs)
    let g' : ↥S' → ↥Z := fun s => ⟨f s, by
      by_cases h1 : (s : K) = 1
      · rw [h1, map_one]; exact Z.one_mem
      · exact hU _ (orderOf_eq_prime (hS'3 s s.2) h1)⟩
    have hg' : Function.Injective g' := by
      intro s s' h
      have h1 : f s = f s' := congrArg Subtype.val h
      exact Subtype.ext (hinjP _ (hS'P s.2) _ (hS'P s'.2) h1)
    have : Finite ↥Z := Nat.finite_of_card_ne_zero (by omega)
    have := Nat.card_le_card_of_injective g' hg'
    rw [hS'card, hZ] at this
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(P : Subgroup K))
  have hPg : ∀ x ∈ (P : Subgroup K), ∃ n : ℤ, x = (g : K) ^ n := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact ⟨n, by simpa using (congrArg Subtype.val hn).symm⟩
  have hφP : ∀ x ∈ (P : Subgroup K), φ x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨x, hx⟩
    have h1 : x ^ (3 ^ k) = 1 := by
      have := pow_orderOf_eq_one (⟨x, hx⟩ : ↥(P : Subgroup K))
      rw [hk] at this
      exact congrArg Subtype.val this
    have h2 : φ x ^ (3 ^ k) = 1 := by rw [← map_pow, h1, map_one]
    rcases Int.units_eq_one_or (φ x) with h | h
    · exact h
    · rw [h, Odd.neg_one_pow (Odd.pow (by decide))] at h2
      exact absurd h2 (by decide)
  have hπg : π g ≠ 1 := by
    intro h1
    have hPM : (P : Subgroup K) ≤ π.ker := by
      intro x hx
      obtain ⟨n, rfl⟩ := hPg x hx
      rw [MonoidHom.mem_ker, map_zpow, h1, one_zpow]
    have h6 : π.ker.index = 6 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top,
        Nat.card_perm]
      simp [Nat.card_eq_fintype_card, Nat.factorial]
    have h7 := Subgroup.index_dvd_of_le hPM
    rw [h6] at h7
    exact P.not_dvd_index (Nat.dvd_trans (by norm_num) h7)
  have hPA : (P : Subgroup K) ≤ φ.ker := fun x hx => MonoidHom.mem_ker.2 (hφP x hx)
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have hfrat := Sylow.normalizer_sup_eq_top (P.subtype hPA)
  have hmapP : Subgroup.map φ.ker.subtype ((P.subtype hPA : Sylow 3 ↥φ.ker) : Subgroup ↥φ.ker) =
      (P : Subgroup K) := Subgroup.map_subgroupOf_eq_of_le hPA
  rw [hmapP] at hfrat
  obtain ⟨t, htN, htA⟩ : ∃ t ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), t ∉ φ.ker := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ φ.ker := hcon
    have htop : φ.ker = ⊤ := top_unique (hfrat ▸ sup_le hle le_rfl)
    obtain ⟨y, hy⟩ := hφ (-1)
    have h1 : φ y = 1 := MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top y)
    rw [hy] at h1
    exact absurd h1 (by decide)
  have hφt : φ t = -1 := by
    rcases Int.units_eq_one_or (φ t) with h | h
    · exact absurd (MonoidHom.mem_ker.2 h) htA
    · exact h
  have htg : t * (g : K) * t⁻¹ ∈ (P : Subgroup K) :=
    (Subgroup.mem_normalizer_iff.1 htN _).1 g.2
  obtain ⟨a, ha⟩ := hPg _ htg
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' g
  have hgK : orderOf (g : K) = 3 ^ j := by rw [Subgroup.orderOf_coe]; exact hj
  have hg1 : (g : K) ≠ 1 := fun h => hπg (by
    have : π (g : K) = 1 := by rw [h, map_one]
    exact this)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hgK))
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hz₀ord : orderOf ((g : K) ^ (3 ^ j')) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hgK]; exact pow_dvd_pow 3 (Nat.le_succ j')), hgK, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hz₀P : (g : K) ^ (3 ^ j') ∈ (P : Subgroup K) := Subgroup.pow_mem _ g.2 _
  have hconj : t * (g : K) ^ (3 ^ j') * t⁻¹ = (g : K) ^ (3 ^ j') := by
    refine hinjP _ ((Subgroup.mem_normalizer_iff.1 htN _).1 hz₀P) _ hz₀P ?_
    rw [map_mul, map_mul, map_inv]
    have := hcent t _ (hU _ hz₀ord)
    rw [this, mul_inv_cancel_right]
  have h1 : (g : K) ^ (a * ((3 ^ j' : ℕ) : ℤ)) = (g : K) ^ ((3 ^ j' : ℕ) : ℤ) := by
    have h2 := conj_pow (a := t) (b := (g : K)) (i := 3 ^ j')
    rw [ha, hconj, ← zpow_natCast, ← zpow_mul] at h2
    rw [h2, zpow_natCast]
  have h3 : (g : K) ^ ((a - 1) * ((3 ^ j' : ℕ) : ℤ)) = 1 := by
    rw [sub_mul, one_mul, zpow_sub, h1, mul_inv_cancel]
  have h4 : ((3 * 3 ^ j' : ℕ) : ℤ) ∣ (a - 1) * ((3 ^ j' : ℕ) : ℤ) := by
    have h5 := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hgK, pow_succ'] at h5
    exact h5
  have h5 : (3 : ℤ) ∣ a - 1 := by
    have hn : ((3 ^ j' : ℕ) : ℤ) ≠ 0 := by positivity
    have h6 : (3 : ℤ) * ((3 ^ j' : ℕ) : ℤ) ∣ (a - 1) * ((3 ^ j' : ℕ) : ℤ) := by
      simpa [Nat.cast_mul] using h4
    exact (mul_dvd_mul_iff_right hn).1 h6
  set c : Equiv.Perm (Fin 3) := π (g : K) with hc
  have hcsign : Equiv.Perm.sign c = 1 := hφP g g.2
  have hc3' : c ^ 3 = 1 := hc3 c hcsign
  obtain ⟨m, hm⟩ := h5
  have hca : c ^ a = c := by
    have hae : a = 3 * m + 1 := by omega
    rw [hae, zpow_add, zpow_one, zpow_mul]
    simp [hc3']
  have hconj2 : π (t * (g : K) * t⁻¹) = c⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    exact hinv c (π t) hcsign hφt
  have hconj3 : π (t * (g : K) * t⁻¹) = c ^ a := by rw [ha, map_zpow]
  have hcinv : c⁻¹ = c := by rw [← hconj2, hconj3, hca]
  have hc2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [hcinv]
      _ = 1 := mul_inv_cancel c
  have hc1 : c = 1 := by
    have : c ^ 3 = c := by rw [pow_succ, pow_two, hc2, one_mul]
    rw [← this, hc3']
  exact hπg hc1

theorem pRank_le_pRank_map {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (f : G →* G') (hf : IsPGroup q f.ker)
    (H : Subgroup G) : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hdisj : Disjoint E f.ker := IsPGroup.disjoint_of_ne p q hpq E f.ker hEp hf
  have hinj : Function.Injective (f.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : G) ∈ f.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 h1)
  have := hE.1
  refine le_pRank_of_injective hp.out.one_lt (A := ↥E) (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 a a.2)) hcard (f.comp E.subtype) hinj ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x, hEH x.2, rfl⟩

theorem exists_subgroup_card_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (h : 1 ≤ CFSG.Open.pRank p H) :
    ∃ X : Subgroup G, X ≤ H ∧ IsElemAbelian p X ∧ Nat.card X = p := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.out.one_lt)
  obtain ⟨x, hx⟩ := exists_ne (1 : E)
  have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hxp : (x : G) ^ p = 1 := hE.2 x x.2
  refine ⟨Subgroup.zpowers (x : G), (Subgroup.zpowers_le.2 x.2).trans hEH, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro y ⟨n, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]

theorem eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {R : Subgroup G} (hR : ¬ p ∣ Nat.card R) {e : G} (he : e ∈ R) (hep : e ^ p = 1) : e = 1 := by
  have h1 : orderOf e ∣ p := orderOf_dvd_of_pow_eq_one hep
  have h2 : orderOf e ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R he
  rcases (Nat.dvd_prime hp.out).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hR

end A320

end CFSG.Quasithin
