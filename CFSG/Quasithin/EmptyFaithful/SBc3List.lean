module

public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.EmptyFaithful.R3cSL2
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

namespace SBc3

section Small

theorem false_of_card_dvd_six {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (h : Nat.card X ∣ 6) : False := by
  have : Group.IsPerfect X := hq.1
  have hperf : commutator X = ⊤ := Group.IsPerfect.commutator_eq_top
  have hnc : ¬ ∀ a b : X, a * b = b * a := by
    intro hc
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq
    exact hab (hc a b)
  have hnt : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq
    exact ⟨⟨a, b, fun hh => hab (by rw [hh])⟩⟩
  have hd : Nat.card X ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨h, by norm_num⟩
  have hd' : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hd'] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h1 | h2 | h3 | h6
  · have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 h1).1
    exact not_subsingleton X this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic X := isCyclic_of_prime_card h2
    let _ := IsCyclic.commGroup (α := X)
    exact hnc fun a b => mul_comm a b
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic X := isCyclic_of_prime_card h3
    let _ := IsCyclic.commGroup (α := X)
    exact hnc fun a b => mul_comm a b
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [h6]; norm_num)
    set P : Subgroup X := Subgroup.zpowers g with hP
    have hPc : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hg]
    have hidx : P.index = 2 := by
      have := P.card_mul_index
      rw [hPc, h6] at this
      omega
    have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
    have hQc : Nat.card (X ⧸ P) = 2 := by rw [← Subgroup.index, hidx]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (X ⧸ P) := isCyclic_of_prime_card hQc
    let _ := IsCyclic.commGroup (α := X ⧸ P)
    have hk := Abelianization.commutator_subset_ker (QuotientGroup.mk' P)
    rw [hperf] at hk
    have hPtop : P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have := hk (Subgroup.mem_top x)
      rwa [QuotientGroup.ker_mk'] at this
    rw [hPtop, Subgroup.index_top] at hidx
    omega

end Small

section Subnormal

variable {Ω : Type} [Group Ω]

theorem isSubnormal_subgroupOf {K X : Subgroup Ω} (h : IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal := by
  have h1 := A3.subnormal_comap X.subtype h
  have e2 : X.comap X.subtype = ⊤ := by ext x; simp
  rw [e2] at h1
  exact A3.subnormal_top_iff.1 h1

theorem ne_bot_of_isQuasisimple {K : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K) : K ≠ ⊥ := by
  rintro rfl
  exact InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => by
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem eq_of_subnormal_of_isSimpleGroup {K X : Subgroup Ω} (hX : IsSimpleGroup ↥X) (hKX : K ≤ X)
    (hsn : (K.subgroupOf X).IsSubnormal) (hK : K ≠ ⊥) : K = X := by
  rcases hsn.eq_bot_or_top_of_isSimpleGroup hX with h | h
  · exfalso
    apply hK
    rw [eq_bot_iff]
    intro k hk
    have h2 : (⟨k, hKX hk⟩ : ↥X) ∈ K.subgroupOf X := hk
    rw [h, Subgroup.mem_bot] at h2
    have := congrArg Subtype.val h2
    simpa using this
  · exact le_antisymm hKX (Subgroup.subgroupOf_eq_top.1 h)

theorem gwQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.GorensteinWalter.IsQuasisimple Q := by
  have : Group.IsPerfect Q := h.1
  obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple h
  exact ⟨⟨⟨a, b, fun hh => hab (by rw [hh])⟩⟩, Group.IsPerfect.commutator_eq_top, h.2.1⟩

theorem le_or_le_of_subnormal {J K G₁ G₂ : Subgroup Ω} [Finite Ω] (hKJ : K ≤ J)
    (hsn : IsSubnormal K J) (hK : CFSG.IsQuasisimple ↥K) (h₁ : G₁ ≤ J) (h₂ : G₂ ≤ J)
    (hn₁ : (G₁.subgroupOf J).Normal) (hn₂ : (G₂.subgroupOf J).Normal) (hKG : K ≤ G₁ ⊔ G₂) :
    K ≤ G₁ ∨ K ≤ G₂ := by
  have hKc : CFSG.GorensteinWalter.IsComponentOf K J :=
    ⟨hKJ, isSubnormal_subgroupOf hsn, gwQuasisimple hK⟩
  rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf h₁
    hn₁.isSubnormal hKc with h | hc₁
  · exact Or.inl h
  rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf h₂
    hn₂.isSubnormal hKc with h | hc₂
  · exact Or.inr h
  exfalso
  have hle₁ : G₁ ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc₁
  have hle₂ : G₂ ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc₂
  have hKC : K ≤ Subgroup.centralizer (K : Set Ω) := hKG.trans (sup_le hle₁ hle₂)
  exact InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hKC ha) b hb).symm

theorem conj_mem_of_mem_sup_zpowers {G₁ G₂ : Subgroup Ω} {t : Ω}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (ht₁ : t ∈ Subgroup.normalizer (G₁ : Set Ω)) (ht₂ : t ∈ Subgroup.normalizer (G₂ : Set Ω)) :
    ∀ x ∈ (G₁ ⊔ G₂) ⊔ Subgroup.zpowers t, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := by
  intro x hx g hg
  have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Ω) : Set Ω) :=
    InternalSec.mem_normalizer_sup ht₁ ht₂
  obtain ⟨m, hm, s, hs, rfl⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (Subgroup.zpowers_le.2 htN)).1 hx
  have hz : Subgroup.zpowers t ≤ Subgroup.normalizer (G₁ : Set Ω) := Subgroup.zpowers_le.2 ht₁
  have e2 : m * s * g * (m * s)⁻¹ = m * (s * g * s⁻¹) * m⁻¹ := by group
  rw [e2]
  exact InternalSec.conj_mem_of_mem_sup_of_commute hcomm m hm _
    ((Subgroup.mem_normalizer_iff.mp (hz hs) g).mp hg)

end Subnormal

section Factors

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qlist_of_sl2 {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥X ≃* ↥(StatedSL 2 F)) : B56QuasisimpleList ↥K := by
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup ↥X := by
      have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      exact e.isSimpleGroup
    have hKeq : K = X := eq_of_subnormal_of_isSimpleGroup hsimple hKX hsn (ne_bot_of_isQuasisimple hK)
    exact Or.inl ⟨n, F, inferInstance, inferInstance, hF, ⟨(MulEquiv.subgroupCongr hKeq).trans e⟩⟩
  · exfalso
    have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have hX : Nat.card ↥X = 6 := by
      rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
      norm_num
    exact false_of_card_dvd_six hK (hX ▸ Subgroup.card_dvd_of_le hKX)

omit [Finite Ω] in
theorem qlist_of_sl3 {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) {m : ℕ} {F : Type} [Field F] [Finite F] (hm : Odd m)
    (hF : Nat.card F = 2 ^ m) (e : ↥X ≃* ↥(StatedSL 3 F)) : B56QuasisimpleList ↥K := by
  have hsimple : IsSimpleGroup ↥X := by
    have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hm
    exact e.isSimpleGroup
  have hKeq : K = X := eq_of_subnormal_of_isSimpleGroup hsimple hKX hsn (ne_bot_of_isQuasisimple hK)
  exact Or.inr (Or.inl ⟨m, F, inferInstance, inferInstance, hF, ⟨(MulEquiv.subgroupCongr hKeq).trans e⟩⟩)

omit [Finite Ω] in
theorem qlist_of_sl3_two {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) (e : ↥X ≃* ↥(StatedSL 3 (ZMod 2))) : B56QuasisimpleList ↥K :=
  qlist_of_sl3 hKX hsn hK (m := 1) (F := ZMod 2) odd_one (by simp) e

omit [Finite Ω] in
theorem qlist_of_alt6 {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) (e : ↥X ≃* ↥(alternatingGroup (Fin 6))) : B56QuasisimpleList ↥K := by
  have hsimple : IsSimpleGroup ↥X := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hKeq : K = X := eq_of_subnormal_of_isSimpleGroup hsimple hKX hsn (ne_bot_of_isQuasisimple hK)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hKeq).trans e⟩))))

omit [Finite Ω] in
theorem qlist_of_perm_five {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) (e : ↥X ≃* Equiv.Perm (Fin 5)) : B56QuasisimpleList ↥K := by
  set Kp : Subgroup (Equiv.Perm (Fin 5)) := (K.subgroupOf X).map e.toMonoidHom with hKp
  have hsnp : Kp.IsSubnormal := Subgroup.IsSubnormal.map e.surjective hsn
  have eK : ↥K ≃* ↥Kp := (Subgroup.subgroupOfEquivOfLe hKX).symm.trans
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
  have hKq : CFSG.IsQuasisimple ↥Kp := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK
  have hperfp : Group.IsPerfect ↥Kp := hKq.1
  have hKpA : Kp ≤ alternatingGroup (Fin 5) := by
    intro p hp
    set f : ↥Kp →* ℤˣ := Equiv.Perm.sign.comp Kp.subtype
    have h1 := Abelianization.commutator_subset_ker f
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact Equiv.Perm.mem_alternatingGroup.2 (h1 (Subgroup.mem_top ⟨p, hp⟩))
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hKpeq : Kp = alternatingGroup (Fin 5) :=
    eq_of_subnormal_of_isSimpleGroup hsimple hKpA hsnp.subgroupOf (ne_bot_of_isQuasisimple hKq)
  have eA : ↥K ≃* ↥(alternatingGroup (Fin 5)) := eK.trans (MulEquiv.subgroupCongr hKpeq)
  obtain ⟨e₀, -⟩ := A5Model.exists_mulEquiv_A5_SL2_four
  exact Or.inl ⟨2, GaloisField 2 2, inferInstance, inferInstance, by simpa using A5Model.card_gf4,
    ⟨eA.trans (e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
      (GaloisField 2 2)))⟩⟩

theorem qlist_of_image_sl2 {K X : Subgroup Ω} (hKX : K ≤ X) (hsn : (K.subgroupOf X).IsSubnormal)
    (hK : CFSG.IsQuasisimple ↥K) {n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (π : ↥(StatedSL 2 F) →* ↥X) (hπ : Function.Surjective π) : B56QuasisimpleList ↥K := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial F)
      simp [hF] at this
    · exact hn
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup ↥(StatedSL 2 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    have hker : π.ker = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal π.ker with h | h
      · exact h
      · exfalso
        have hX : X = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨g, hg⟩ := hπ ⟨x, hx⟩
          have : g ∈ π.ker := by rw [h]; exact Subgroup.mem_top g
          rw [MonoidHom.mem_ker] at this
          rw [this] at hg
          have := congrArg Subtype.val hg
          simpa using this.symm
        exact ne_bot_of_isQuasisimple hK (eq_bot_iff.2 (hX ▸ hKX))
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
    exact qlist_of_sl2 hKX hsn hK hn hF (MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm
  · exfalso
    have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have hS : Nat.card ↥(StatedSL 2 F) = 6 := by
      rw [R3c.card_statedSL_two_pow hF]
      norm_num
    have hX : Nat.card ↥X ∣ 6 := hS ▸ Subgroup.card_dvd_of_surjective hπ
    exact false_of_card_dvd_six hK ((Subgroup.card_dvd_of_le hKX).trans hX)

end Factors

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem normal_of_commute {G₁ G₂ : Subgroup (MulAut V)} (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    (G₁.subgroupOf (G₁ ⊔ G₂)).Normal ∧ (G₂.subgroupOf (G₁ ⊔ G₂)).Normal := by
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  refine ⟨(Subgroup.normal_subgroupOf_iff le_sup_left).2 fun h k hh hk =>
    InternalSec.conj_mem_of_mem_sup_of_commute hc k hk h hh,
    (Subgroup.normal_subgroupOf_iff le_sup_right).2 fun h k hh hk => ?_⟩
  have hk' : k ∈ G₂ ⊔ G₁ := by rw [sup_comm]; exact hk
  exact InternalSec.conj_mem_of_mem_sup_of_commute hc' k hk' h hh

theorem b56QL_of_subnormal {J K : Subgroup (MulAut V)} (hKJ : K ≤ J) (hsn : IsSubnormal K J)
    (hK : CFSG.IsQuasisimple ↥K)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56QuasisimpleList ↥K := by
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  ·
    obtain ⟨hEq, -, hlist⟩ := h1
    have hKE : K ≤ quasithinGenFitting J :=
      le_sup_of_le_right (le_sSup ⟨hKJ, hsn, B1Red.isQuasisimple_to_open hK⟩)
    have hEJ := quasithinGenFitting_le J
    have hsnE : IsSubnormal K (quasithinGenFitting J) := A3.subnormal_of_le_of_le hsn hKE hEJ
    rcases A3.eq_top_or_le_center_of_subnormal hEq (isSubnormal_subgroupOf hsnE) with h | h
    · have hKeq : K = quasithinGenFitting J := le_antisymm hKE (Subgroup.subgroupOf_eq_top.1 h)
      rw [hKeq]
      exact hlist
    · exfalso
      refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
      have h1 : (⟨a, hKE ha⟩ : ↥(quasithinGenFitting J)) ∈
          Subgroup.center ↥(quasithinGenFitting J) :=
        h (show (⟨a, hKE ha⟩ : ↥(quasithinGenFitting J)) ∈ K.subgroupOf (quasithinGenFitting J) from ha)
      have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
      exact (congrArg Subtype.val h2).symm
  · exact (InternalSec.not_le_perm_three hK hKJ e).elim
  ·
    subst hsup
    obtain ⟨hn₁, hn₂⟩ := normal_of_commute hc
    rcases le_or_le_of_subnormal hKJ hsn hK le_sup_left le_sup_right hn₁ hn₂ hKJ with h | h
    · have hsn₁ := isSubnormal_subgroupOf (A3.subnormal_of_le_of_le hsn h le_sup_left)
      rcases hf₁ with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, -, hm, hF, ⟨e⟩⟩
      · exact qlist_of_sl2 h hsn₁ hK hn hF e
      · exact qlist_of_perm_five h hsn₁ hK e
      · exact qlist_of_sl3 h hsn₁ hK hm hF e
    · have hsn₂ := isSubnormal_subgroupOf (A3.subnormal_of_le_of_le hsn h le_sup_right)
      rcases hf₂ with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, -, hm, hF, ⟨e⟩⟩
      · exact qlist_of_sl2 h hsn₂ hK hn hF e
      · exact qlist_of_perm_five h hsn₂ hK e
      · exact qlist_of_sl3 h hsn₂ hK hm hF e
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      InternalSec.mem_normalizer_sup ht₁ ht₂
    have hKG : K ≤ G₁ ⊔ G₂ := by
      have h1 : K ≤ ⁅J, J⁆ := InternalSec.le_commutator_of_perfect hKJ hK.1
      rw [hJt] at h1
      exact h1.trans (InternalSec.commutator_le_of_zpowers htN)
    have h₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have h₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    have hn₁ : (G₁.subgroupOf J).Normal := by
      refine (Subgroup.normal_subgroupOf_iff h₁J).2 fun h k hh hk => ?_
      rw [hJt] at hk
      exact conj_mem_of_mem_sup_zpowers hc ht₁ ht₂ k hk h hh
    have hn₂ : (G₂.subgroupOf J).Normal := by
      refine (Subgroup.normal_subgroupOf_iff h₂J).2 fun h k hh hk => ?_
      rw [hJt, sup_comm G₁ G₂] at hk
      exact conj_mem_of_mem_sup_zpowers hc' ht₂ ht₁ k hk h hh
    rcases le_or_le_of_subnormal hKJ hsn hK h₁J h₂J hn₁ hn₂ hKG with h | h
    · exact qlist_of_alt6 h (isSubnormal_subgroupOf (A3.subnormal_of_le_of_le hsn h h₁J)) hK e₁
    · exact (InternalSec.not_le_of_card_prime hK h hc₂).elim
  ·
    subst hsup
    obtain ⟨hn₁, hn₂⟩ := normal_of_commute hc
    rcases le_or_le_of_subnormal hKJ hsn hK le_sup_left le_sup_right hn₁ hn₂ hKJ with h | h
    · exact qlist_of_sl3_two h (isSubnormal_subgroupOf (A3.subnormal_of_le_of_le hsn h le_sup_left))
        hK e₁
    · have hsn₂ := isSubnormal_subgroupOf (A3.subnormal_of_le_of_le hsn h le_sup_right)
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
      · exact qlist_of_sl3_two h hsn₂ hK e₂
      · exact qlist_of_image_sl2 h hsn₂ hK hF π hR.1

end Main

section Module

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem omegaOneCenter_le_Sgp153 (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

theorem isTwoReduced_UI (c : Ctx15325 T Mc M V₁ V₂ Yp I t) (hF : Facts153 T M V₁ Yp I) :
    IsElemAbelian 2 (UI153 T I) ∧ IsTwoReducedIn I (UI153 T I) := by
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hZ := omegaOneCenter_le_Sgp153 c.hyp
  exact ⟨(conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 c.charTwo hZ).2,
    isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 c.charTwo hZ⟩

end Module

section Offenders

variable {G : Type} [Group G] [Finite G] {W I : Subgroup G} [IsMulCommutative ↥W]

theorem autOn_thompsonJ_le_ffJ (hWe : IsElemAbelian 2 W) (hWI : W ≤ I)
    (hIN : I ≤ Subgroup.normalizer (W : Set G)) :
    autOn (thompsonJ I) W ≤ ffJ (autOn I W) := by
  have hAJ : ∀ A : Subgroup G, IsMaxElemAbelian I A → autOn A W ≤ ffJ (autOn I W) := by
    intro A hA
    by_cases hAC : A ≤ Subgroup.centralizer (W : Set G)
    · have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0]
      exact bot_le
    · have hoff : IsFFOffender I W A := ⟨hA, hAC⟩
      exact B6.le_ffJ (offenderImages_isFFStarOffender hWe hWI hIN ⟨A, hoff, rfl⟩)
  set D : Subgroup G := ((ffJ (autOn I W)).comap (conjAct W)).map
    (Subgroup.normalizer (W : Set G)).subtype with hD
  have hJD : thompsonJ I ≤ D := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (W : Set G) := hIN (hA.1 ha)
    exact ⟨⟨a, haN⟩, hAJ A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
  intro φ hφ
  obtain ⟨⟨g, hgN⟩, hgJ, rfl⟩ := Setup.mem_autOn_iff.1 hφ
  obtain ⟨n, hn, hng⟩ := hJD hgJ
  have hnn : n = ⟨g, hgN⟩ := Subtype.ext hng
  rw [hnn] at hn
  exact hn

theorem autOn_mem_list_of_component {L : Subgroup G} (h56 : AsB56) (hWe : IsElemAbelian 2 W)
    (hred : IsTwoReducedIn I W) (hSQ : SQTKGroup ↥I) (hLJ : L ∈ cComp (thompsonJ I))
    (hq : CFSG.IsQuasisimple ↥(autOn L W)) : B56QuasisimpleList ↥(autOn L W) := by
  have hIN : I ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hWI : W ≤ I := hred.1
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLJ
  have hLJ' : L ≤ thompsonJ I := le_of_mem_cComp hLJ
  have hO2 : pCoreOf 2 (autOn I W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hKJ : autOn L W ≤ ffJ (autOn I W) :=
    (InternalSec.autOn_le_autOn_of_le hLJ').trans (autOn_thompsonJ_le_ffJ hWe hWI hIN)
  have hKne : autOn L W ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hJne : ffJ (autOn I W) ≠ ⊥ := fun h => hKne (le_bot_iff.1 (h ▸ hKJ))
  have hV : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hWe.2 v v.2)
  have hcases := h56 ↥W hV (ffJ (autOn I W)) hJne (InternalSec.b53Hyp_ffJ_autOn hIN hSQ hO2)
  have hsnI : IsSubnormal L I := hLI.2.2.1
  have hsnX : IsSubnormal (autOn L W) (autOn I W) := by
    have h1 := A3.subnormal_comap (Subgroup.normalizer (W : Set G)).subtype hsnI
    exact A3.subnormal_map (conjAct W) h1
  have hsnJ : IsSubnormal (autOn L W) (ffJ (autOn I W)) :=
    A3.subnormal_of_le_of_le hsnX hKJ (B6.ffJ_le _)
  exact b56QL_of_subnormal hKJ hsnJ hq hcases

end Offenders

section Star

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem star_mem_list (h56 : AsB56) (c : Ctx15325 T Mc M V₁ V₂ Yp I t) (hF : Facts153 T M V₁ Yp I)
    (hLJ : L ∈ cComp (thompsonJ I)) (hq : CFSG.IsQuasisimple ↥(autOn L (UI153 T I))) :
    B56QuasisimpleList ↥(Star153 T I L) := by
  obtain ⟨hWe, hred⟩ := isTwoReduced_UI c hF
  have : IsMulCommutative ↥(UI153 T I) := hWe.1
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot c.hyp.hyp.qtfe.qtke c.hyp.hyp.qtfe.simple
      c.hyp.hyp.qtfe.nonabelian c.inH.1.2
  exact autOn_mem_list_of_component h56 hWe hred hSQ hLJ hq

theorem input27List_holds (h56 : AsB56) : Input27List := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  exact star_mem_list h56 c.ctx c.facts.toFacts153 c.conc.1 c.conc.2.2.2.2.1

end Star

end SBc3

end CFSG.Quasithin
