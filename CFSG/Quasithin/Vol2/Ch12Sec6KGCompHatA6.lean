module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompResid
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompDescend
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.Item19Res4Proof
open CFSG.FiveTransitive.CharacteristicAutomorphism (quotient)
open scoped commutatorElement

theorem perm_six_pow_three_of_pow_nine : ∀ σ : Perm (Fin 6), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  decide +kernel

theorem perm_six_exists_odd_commute : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 →
    ∃ τ : Perm (Fin 6), Perm.sign τ = -1 ∧ τ * σ = σ * τ := by
  decide +kernel

theorem cycleType_eq_replicate_of_cube {n : ℕ} {σ : Perm (Fin n)} (h3 : σ ^ 3 = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 := by
  rw [Multiset.eq_replicate]
  refine ⟨rfl, fun m hm => ?_⟩
  have h1 := two_le_of_mem_cycleType hm
  have h3' : m ∣ 3 := (dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one h3)
  rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h <;> omega

theorem card_centralizer_perm_six_three {σ : Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 6)))) = 18 := by
  have hct := cycleType_eq_replicate_of_cube h3
  set k := Multiset.card σ.cycleType with hk
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_iff_ne_zero, Ne, card_cycleType_eq_zero]
    exact h1
  have hsum : σ.cycleType.sum = 3 * k := by
    rw [hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 3 * k ≤ 6 := by
    have := sum_cycleType_le σ
    rw [hsum, Fintype.card_fin] at this
    exact this
  have htf : (Multiset.replicate k 3).toFinset = {3} := by
    rw [Multiset.toFinset_replicate]
    split_ifs with h0
    · omega
    · rfl
  have hk2 : k ≤ 2 := by omega
  rw [nat_card_centralizer, Fintype.card_fin, hsum, hct, Multiset.prod_replicate, htf,
    Finset.prod_singleton, Multiset.count_replicate_self]
  interval_cases k <;> rfl

theorem card_centralizer_alt6_three {a : alternatingGroup (Fin 6)} (h3 : a ^ 3 = 1)
    (h1 : a ≠ 1) :
    Nat.card (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6)))) = 9 := by
  classical
  have hσ3 : (a : Perm (Fin 6)) ^ 3 = 1 := by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  have hσ1 : (a : Perm (Fin 6)) ≠ 1 := fun h => h1 (Subtype.ext h)
  set C := Subgroup.centralizer ({(a : Perm (Fin 6))} : Set (Perm (Fin 6))) with hC
  have h18 : Nat.card C = 18 := card_centralizer_perm_six_three hσ3 hσ1
  obtain ⟨τ, hτs, hτc⟩ := perm_six_exists_odd_commute _ hσ3
  set f : ↥C →* ℤˣ := Perm.sign.comp C.subtype with hf
  have hfs : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨τ, Subgroup.mem_centralizer_singleton_iff.mpr hτc⟩, hτs⟩
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfs, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hk : Nat.card f.ker = 9 := by
    have := f.ker.card_mul_index
    rw [hidx, h18] at this
    omega
  rw [← hk]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨(x : alternatingGroup (Fin 6)),
          Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2))⟩,
        MonoidHom.mem_ker.mpr (mem_alternatingGroup.mp (x : alternatingGroup (Fin 6)).2)⟩
      invFun := fun y => ⟨⟨((y : ↥C) : Perm (Fin 6)),
          mem_alternatingGroup.mpr (MonoidHom.mem_ker.mp y.2)⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.mp (y : ↥C).2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem pow_three_eq_one_of_mem_centralizer_alt6 {a y : alternatingGroup (Fin 6)}
    (h3 : a ^ 3 = 1) (h1 : a ≠ 1)
    (hy : y ∈ Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6)))) : y ^ 3 = 1 := by
  have h9 : (⟨y, hy⟩ : Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6)))) ^ 9 = 1 := by
    rw [← card_centralizer_alt6_three h3 h1]
    exact pow_card_eq_one'
  have h9' : (y : Perm (Fin 6)) ^ 9 = 1 := by
    have := congrArg (fun z : Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6))) =>
      ((z : alternatingGroup (Fin 6)) : Perm (Fin 6))) h9
    simpa using this
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact perm_six_pow_three_of_pow_nine _ h9'

theorem eq_one_of_fix_alt6 {ν : MulAut (alternatingGroup (Fin 6))}
    {E S : Subgroup (alternatingGroup (Fin 6))} (hE : Nat.card E = 9) (hS : Nat.card S = 8)
    (hEν : ∀ x ∈ E, ν x = x) (hSν : ∀ x ∈ S, ν x = x) : ν = 1 := by
  set F := MonoidHom.eqLocus ν.toMonoidHom (MonoidHom.id (alternatingGroup (Fin 6))) with hFdef
  have hEF : E ≤ F := fun x hx => hEν x hx
  have hSF : S ≤ F := fun x hx => hSν x hx
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have h72 : 72 ∣ Nat.card F :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 8)
      (hE ▸ Subgroup.card_dvd_of_le hEF) (hS ▸ Subgroup.card_dvd_of_le hSF)
  have hFtop : F = ⊤ := by
    by_contra hF
    have := alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
    have hidx : F.index ≤ 5 := by
      have h1 := F.card_mul_index
      rw [hcardA] at h1
      obtain ⟨c, hc⟩ := h72
      rw [hc] at h1
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0] at h1; omega
        · exact h0
      have : 72 * F.index ≤ 360 := by nlinarith
      omega
    have := index_gt_of_simple hF hidx
    rw [hcardA] at this
    norm_num [Nat.factorial] at this
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ F := hFtop ▸ Subgroup.mem_top x
  exact hx

theorem hind_of_not_mem_zpowers {G : Type*} [Group G] {a b : G} (ha1 : a ≠ 1) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hbn : b ∉ Subgroup.zpowers a) :
    ∀ i j : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
  intro i j hij
  have hbj : b ^ (j : ℕ) ∈ Subgroup.zpowers a := by
    rw [eq_inv_of_mul_eq_one_right hij]
    exact inv_mem (pow_mem (Subgroup.mem_zpowers a) _)
  have hj : j = 0 := by
    fin_cases j
    · rfl
    · exfalso
      apply hbn
      simpa using hbj
    · exfalso
      apply hbn
      have hb4 : b = (b ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hb, one_mul]
      rw [hb4]
      exact pow_mem (by simpa using hbj) 2
  subst hj
  refine ⟨?_, rfl⟩
  have hai : a ^ (i : ℕ) = 1 := by simpa using hij
  fin_cases i
  · rfl
  · exfalso
    apply ha1
    simpa using hai
  · exfalso
    apply ha1
    have hai' : a ^ 2 = 1 := by simpa using hai
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha, hai', inv_one, one_mul]

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem exists_elemAbelian_nine_le_closure {G : Type*} [Group G] [Finite G] {a b : G}
    (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hind : ∀ i j : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = 1 → i = 0 ∧ j = 0) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ E ≤ Subgroup.closure {a, b} := by
  set H := Subgroup.closure ({a, b} : Set G)
  have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert a {b})
  have hbH : b ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine (G := ↥H) (a := ⟨a, haH⟩) (b := ⟨b, hbH⟩)
    (Subtype.ext hab) (Subtype.ext (by rw [Subgroup.coe_pow]; exact ha))
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact hb))
    (fun i j hij => hind i j (by
      have := congrArg Subtype.val hij
      rwa [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one] at this))
  exact ⟨E.map H.subtype, isElemAbelian_map _ hE,
    by rw [Subgroup.card_map_of_injective H.subtype_injective, hE9], Subgroup.map_subtype_le E⟩

theorem commutatorElement_mul_right_of_mem_center {G : Type*} [Group G] {x y z : G}
    (hz : ⁅x, z⁆ ∈ Subgroup.center G) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hc := Subgroup.mem_center_iff.mp hz y
  simp only [commutatorElement_def] at hc ⊢
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ =
      x * y * x⁻¹ * y⁻¹ * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    _ = x * y * x⁻¹ * y⁻¹ * (x * z * x⁻¹ * z⁻¹ * y * y⁻¹) := by rw [hc]
    _ = x * y * x⁻¹ * y⁻¹ * (x * z * x⁻¹ * z⁻¹) := by group

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_hatA6 (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hK : IsHat ↥K (alternatingGroup (Fin 6))) : False := by
  classical
  have := hQ.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hq, hZ3, ⟨φ⟩⟩ := hK
  have h3A6 : CFSG.RankThree.PartTwo.Sec19.IsTripleA6 ↥K := ⟨hZ3, ⟨φ⟩⟩
  have : Group.IsPerfect ↥K := hq.1
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by rw [hZ3]; decide
  have hd := (h.autConf.descend (N := Subgroup.center ↥K) le_rfl hodd).map φ
  by_cases h9 : Nat.card h.rhoP.range = 9
  · refine not_autConf_alt6 hd ?_
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective,
      Subgroup.card_map_of_injective (quotient_injective le_rfl), h9]
  obtain ⟨p, hpP, hpc, hp1⟩ : ∃ p ∈ P, (∀ k ∈ K, p * k = k * p) ∧ p ≠ 1 := by
    by_contra hne
    push Not at hne
    exact h9 (h.card_rhoP_range fun p hp hpc => hne p hp hpc)
  obtain ⟨z₀, hz₀, hz₀1⟩ := exists_mem_center_ne_one h3A6
  obtain ⟨x₀, hx₀3, hx₀Z⟩ := exists_noncentral_of_isTripleA6 h3A6
  have hz₀3 := pow_three_eq_one_of_mem_center h3A6 hz₀
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_elemAbelian_nine (G := ↥K) (a := z₀) (b := x₀)
    (Subgroup.mem_center_iff.mp hz₀ x₀).symm hz₀3 hx₀3
    (hind_of_not_mem_zpowers hz₀1 hz₀3 hx₀3 fun hx => hx₀Z ((Subgroup.zpowers_le.mpr hz₀) hx))
  have hEK : E₀.map K.subtype ≤ K := Subgroup.map_subtype_le E₀
  have hEK9 : Nat.card (E₀.map K.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE₀9]
  have hEKe := isElemAbelian_map K.subtype hE₀
  have hp3 : p ^ 3 = 1 := h.P_elem.2 p hpP
  have hpK : p ∈ K := hEK (mem_of_commute_elemAbelian_nine hQ hEKe hEK9 hp3
    fun e he => hpc e (hEK he))
  set p' : ↥K := ⟨p, hpK⟩ with hp'def
  have hp'Z : p' ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hpc k k.2).symm
  have hp'1 : p' ≠ 1 := fun h1 => hp1 (congrArg Subtype.val h1)
  have hp'3 : p' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hp3)
  have hZp : Subgroup.center ↥K = Subgroup.zpowers p' := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hp'Z)
    rw [hZ3, Nat.card_zpowers, orderOf_eq_prime hp'3 hp'1]
  have hνP : ∀ k : ↥K, (k : Q) ∈ P → h.nu k = k := fun k hk => Subtype.ext (by
    rw [h.coe_nu_apply, h.L_cent k (h.P_le hk), mul_inv_cancel_right])
  have hνZ : ∀ z ∈ Subgroup.center ↥K, h.nu z = z := by
    intro z hz
    rw [hZp] at hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine hνP _ ?_
    rw [Subgroup.coe_zpow]
    exact zpow_mem hpP n
  obtain ⟨p₁, hp₁P, hp₁n⟩ : ∃ p₁ ∈ P, p₁ ∉ Subgroup.zpowers p := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : P ≤ Subgroup.zpowers p)
    rw [h.P_card, Nat.card_zpowers, orderOf_eq_prime hp3 hp1] at this
    norm_num at this
  have hp₁3 : p₁ ^ 3 = 1 := h.P_elem.2 p₁ hp₁P
  have hρ3 : h.rhoP ⟨p₁, hp₁P⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨p₁, hp₁P⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hp₁3)
    rw [this, map_one]
  obtain ⟨k₁, hk₁⟩ := exists_eq_conj_of_isTripleA6 h3A6 _ hρ3
  have hρk : ∀ k : ↥K, (p₁ : Q) * k * p₁⁻¹ = k₁ * k * (k₁ : Q)⁻¹ := by
    intro k
    calc (p₁ : Q) * k * p₁⁻¹ = ((h.rhoP ⟨p₁, hp₁P⟩ k : ↥K) : Q) := rfl
      _ = ((MulAut.conj k₁ k : ↥K) : Q) := by rw [hk₁]
      _ = k₁ * k * (k₁ : Q)⁻¹ := by rw [MulAut.conj_apply]; rfl
  have hk₁3 : k₁ ^ 3 = 1 := by
    apply pow_three_eq_one_of_isTripleA6 h3A6
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj (k₁ ^ 3) = 1 := by rw [map_pow, ← hk₁, hρ3]
    have h2 := DFunLike.congr_fun h1 g
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * k₁ ^ 3 = k₁ ^ 3 * g * (k₁ ^ 3)⁻¹ * k₁ ^ 3 := by rw [h2]
      _ = k₁ ^ 3 * g := by group
  have hpk : Commute p₁ (k₁ : Q) := by
    have h1 := hρk k₁
    calc (p₁ : Q) * k₁ = (p₁ * k₁ * p₁⁻¹) * p₁ := by group
      _ = (k₁ * k₁ * (k₁ : Q)⁻¹) * p₁ := by rw [h1]
      _ = k₁ * p₁ := by group
  set c : Q := p₁ * (k₁ : Q)⁻¹ with hc
  have hck : ∀ k ∈ K, c * k = k * c := by
    intro k hk
    have h1 := hρk (k₁⁻¹ * ⟨k, hk⟩ * k₁)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc c * k = (p₁ * ((k₁ : Q)⁻¹ * k * k₁) * p₁⁻¹) * (p₁ * (k₁ : Q)⁻¹) := by rw [hc]; group
      _ = ((k₁ : Q) * ((k₁ : Q)⁻¹ * k * k₁) * (k₁ : Q)⁻¹) * (p₁ * (k₁ : Q)⁻¹) := by rw [h1]
      _ = k * c := by rw [hc]; group
  have hc3 : c ^ 3 = 1 := by
    have hk₁3' : (k₁ : Q) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hk₁3, Subgroup.coe_one]
    rw [hc, (Commute.inv_right hpk).mul_pow, inv_pow, hk₁3', inv_one, mul_one, hp₁3]
  have hcK : c ∈ K := hEK (mem_of_commute_elemAbelian_nine hQ hEKe hEK9 hc3
    fun e he => hck e (hEK he))
  have hp₁K : p₁ ∈ K := by
    have : p₁ = c * k₁ := by rw [hc, inv_mul_cancel_right]
    rw [this]
    exact mul_mem hcK k₁.2
  set q₁ : ↥K := ⟨p₁, hp₁K⟩ with hq₁def
  have hνq₁ : h.nu q₁ = q₁ := hνP q₁ hp₁P
  have hq₁3 : q₁ ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hp₁3)
  have hq₁Z : q₁ ∉ Subgroup.center ↥K := by
    intro hz
    rw [hZp] at hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hp₁n
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have := congrArg Subtype.val hn
    rwa [Subgroup.coe_zpow] at this
  obtain ⟨E₁, hE₁, hE₁9, hE₁le⟩ := exists_elemAbelian_nine_le_closure (G := ↥K) (a := p') (b := q₁)
    (Subgroup.mem_center_iff.mp hp'Z q₁).symm hp'3 hq₁3
    (hind_of_not_mem_zpowers hp'1 hp'3 hq₁3 fun hx => hq₁Z (hZp ▸ hx))
  have hE₁Q9 : Nat.card (E₁.map K.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE₁9]
  have hE₁Qe := isElemAbelian_map K.subtype hE₁
  set ψ : ↥K →* alternatingGroup (Fin 6) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hψdef
  have hψs : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ k : ↥K, ψ k = 1 ↔ k ∈ Subgroup.center ↥K := by
    intro k
    rw [← QuotientGroup.eq_one_iff]
    constructor
    · intro h1
      exact φ.injective (h1.trans (map_one φ).symm)
    · intro h1
      change φ (QuotientGroup.mk k) = 1
      rw [h1, map_one]
  set νb := MulAut.congr φ (quotient (Subgroup.center ↥K) h.nu) with hνbdef
  have hνbψ : ∀ k : ↥K, νb (ψ k) = ψ (h.nu k) := by
    intro k
    rw [hνbdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    change φ (quotient (Subgroup.center ↥K) h.nu (φ.symm (φ (QuotientGroup.mk k)))) =
      φ (QuotientGroup.mk (h.nu k))
    rw [MulEquiv.symm_apply_apply, quotient_apply_coe]
  set a := ψ q₁ with ha
  have hkey : ∀ y : ↥K, y ^ 3 = 1 → y * q₁ = q₁ * y → ψ y ∈ Subgroup.zpowers a := by
    intro y hy3 hyq
    have hcl : Subgroup.closure ({p', q₁} : Set ↥K) ≤
        Subgroup.centralizer ({y} : Set ↥K) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hp'Z y).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyq.symm
    have hyE : (y : Q) ∈ E₁.map K.subtype := by
      refine mem_of_commute_elemAbelian_nine hQ hE₁Qe hE₁Q9
        (by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]) fun e he => ?_
      obtain ⟨e, he, rfl⟩ := he
      have := Subgroup.mem_centralizer_singleton_iff.mp (hcl (hE₁le he))
      exact (congrArg Subtype.val this).symm
    obtain ⟨y', hy', hyy'⟩ := hyE
    have hy'y : y' = y := Subtype.ext hyy'
    rw [hy'y] at hy'
    have hcl' : Subgroup.closure ({p', q₁} : Set ↥K) ≤ (Subgroup.zpowers a).comap ψ := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · show ψ p' ∈ Subgroup.zpowers a
        rw [(hker p').mpr hp'Z]
        exact one_mem _
      · exact Subgroup.mem_zpowers a
    exact hcl' (hE₁le hy')
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hq₁3, map_one]
  have ha1 : a ≠ 1 := fun h1 => hq₁Z ((hker q₁).mp h1)
  have hνa : νb a = a := by rw [ha, hνbψ, hνq₁]
  obtain ⟨b, hbC, hbn⟩ : ∃ b ∈ Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6))),
      b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx :
      Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6))) ≤ Subgroup.zpowers a)
    rw [card_centralizer_alt6_three ha3 ha1, Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at this
    norm_num at this
  have hba : b * a = a * b := Subgroup.mem_centralizer_singleton_iff.mp hbC
  obtain ⟨bh, rfl⟩ := hψs b
  have hcomm_mem : ∀ y : ↥K, ψ y * a = a * ψ y → ⁅q₁, y⁆ ∈ Subgroup.center ↥K := by
    intro y hy
    rw [← hker, map_commutatorElement, ← ha, commutatorElement_eq_one_iff_mul_comm]
    exact hy.symm
  have hlift3 : ∀ y : ↥K, ψ y * a = a * ψ y → y ^ 3 = 1 := by
    intro y hy
    apply pow_three_eq_one_of_isTripleA6 h3A6
    have h1 : ψ (y ^ 3) = 1 := by
      rw [map_pow]
      exact pow_three_eq_one_of_mem_centralizer_alt6 ha3 ha1
        (Subgroup.mem_centralizer_singleton_iff.mpr hy)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact (hker _).mp h1
  have hw : ⁅q₁, bh⁆ ∈ Subgroup.center ↥K := hcomm_mem bh hba
  have hw1 : ⁅q₁, bh⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact hbn (hkey bh (hlift3 bh hba) h1.symm)
  set ch := bh⁻¹ * h.nu bh with hchdef
  have hνbh : h.nu bh = bh * ch := by rw [hchdef, mul_inv_cancel_left]
  have hνbC : Commute (νb (ψ bh)) a := by
    have h1 := congrArg νb hba
    rw [map_mul, map_mul, hνa] at h1
    exact h1
  have hchC : ψ ch * a = a * ψ ch := by
    have h1 : ψ ch = (ψ bh)⁻¹ * νb (ψ bh) := by rw [hchdef, map_mul, map_inv, hνbψ]
    rw [h1]
    exact ((Commute.inv_left (show Commute (ψ bh) a from hba)).mul_left hνbC).eq
  have hw' : ⁅q₁, ch⁆ ∈ Subgroup.center ↥K := hcomm_mem ch hchC
  have hνw : h.nu ⁅q₁, bh⁆ = ⁅q₁, bh⁆ * ⁅q₁, ch⁆ := by
    rw [map_commutatorElement, hνq₁, hνbh, commutatorElement_mul_right_of_mem_center hw']
  have hw'1 : ⁅q₁, ch⁆ = 1 := by
    have h1 := hνw
    rw [hνZ _ hw] at h1
    exact (mul_eq_left.mp h1.symm)
  rw [commutatorElement_eq_one_iff_mul_comm] at hw'1
  have hchA : ψ ch ∈ Subgroup.zpowers a := hkey ch (hlift3 ch hchC) hw'1.symm
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hchA
  have hνb : νb (ψ bh) = ψ bh * a ^ m := by
    rw [hm, hchdef, map_mul, map_inv, hνbψ, mul_inv_cancel_left]
  have hνν : νb (νb (ψ bh)) = ψ bh := apply_apply_of_sq hd.sq _
  rw [hνb, map_mul, map_zpow, hνa, hνb, mul_assoc, ← zpow_add, mul_eq_left] at hνν
  have ham : a ^ m = 1 := by
    have h3m : a ^ (3 * m) = 1 := by rw [zpow_mul, zpow_ofNat, ha3, one_zpow]
    calc a ^ m = a ^ (3 * m) * (a ^ (m + m))⁻¹ := by
          rw [← zpow_neg, ← zpow_add]
          congr 1
          ring
      _ = 1 := by rw [h3m, hνν, inv_one, one_mul]
  have hνbfix : νb (ψ bh) = ψ bh := by rw [hνb, ham, mul_one]
  have hb3 : ψ bh ^ 3 = 1 := pow_three_eq_one_of_mem_centralizer_alt6 ha3 ha1 hbC
  obtain ⟨E₂, -, hE₂9, hE₂le⟩ := exists_elemAbelian_nine_le_closure (a := a) (b := ψ bh)
    hba.symm ha3 hb3 (hind_of_not_mem_zpowers ha1 ha3 hb3 hbn)
  have hclfix : Subgroup.closure ({a, ψ bh} : Set (alternatingGroup (Fin 6))) ≤
      MonoidHom.eqLocus νb.toMonoidHom (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hνa
    · exact hνbfix
  obtain ⟨S, hS, hSν⟩ := hd.sylow
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hS8 : Nat.card S = 8 := by
    rw [card_eq_of_isSylowTwoOf hS hcardA (by decide)]
    norm_num
  exact hd.ne_one (eq_one_of_fix_alt6 hE₂9 hS8 (fun x hx => hclfix (hE₂le hx)) hSν)

end CFSG.Quasithin.H13.S126C
