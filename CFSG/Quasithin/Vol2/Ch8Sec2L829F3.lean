module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828E
public import CFSG.Quasithin.Vol2.Ch8Sec2D3Inputs
public import CFSG.Quasithin.Background.KnownMultOdd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section L829F3

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_GL32_829 : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

omit [Finite G] in
theorem isCyclic_sylow_of_card_dvd {J : Type*} [Group J] [Finite J] {n : ℕ}
    (hJ : Nat.card J ∣ n) (hn : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ n) {r : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) (P : Sylow r J) : IsCyclic (P : Subgroup J) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hdvd : r ^ k ∣ n := hk ▸ (Subgroup.card_subgroup_dvd_card _).trans hJ
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton ↥(P : Subgroup J) := (Nat.card_eq_one_iff_unique.1 hk).1
      infer_instance
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  · exact absurd ((pow_dvd_pow r hk2).trans hdvd) (hn r hr.out hr2)

theorem not_sq_dvd_168 : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 168 := by
  intro r hr hr2 h1
  have h4 := hr.two_le
  have hcop : Nat.Coprime (r ^ 2) 8 :=
    Nat.Coprime.pow 2 3 ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have h21 : r ^ 2 ∣ 21 := by
    have h168 : (168 : ℕ) = 8 * 21 := by norm_num
    rw [h168] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  have h5 : r ^ 2 ≤ 21 := Nat.le_of_dvd (by norm_num) h21
  have h6 : r ≤ 4 := by nlinarith
  interval_cases r
  · exact hr2 rfl
  · norm_num at h21
  · exact absurd hr (by norm_num)

omit [Finite G] in
theorem le_center_of_normal_829 {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] (hN : N ≠ ⊤) : N ≤ Subgroup.center Q := by
  let π := QuotientGroup.mk' (Subgroup.center Q)
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  have hnormal : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · have hker : N ≤ π.ker := N.map_eq_bot_iff.mp hbot
    simpa only [π, QuotientGroup.ker_mk'] using hker
  · exfalso
    apply hN
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hQ.1.commutator_eq_top] at hderived
    exact top_unique hderived

omit [Finite G] in
theorem isPGroup_ker_and_exists_pow_prime_829 {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X)) {J : Type*} [Group J] [Finite J]
    [IsSimpleGroup J] (ρ : X →* J) (hρs : Function.Surjective ρ) (hJ2 : ¬ IsPGroup 2 J)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (P : Sylow r J),
      IsCyclic (P : Subgroup J)) :
    IsPGroup 2 ↥ρ.ker ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card J → ∃ f : X, f ^ p = 1 ∧ ρ f ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 X with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  have hQρ : Q.map ρ = ⊥ := by
    have hn : (Q.map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρs
    rcases hn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have h2 : IsPGroup 2 ↥(Q.map ρ) := hQ2.map ρ
      rw [h] at h2
      exact hJ2 (h2.of_equiv Subgroup.topEquiv)
  have hQker : Q ≤ ρ.ker := (Subgroup.map_eq_bot_iff _).mp hQρ
  set ρb : X ⧸ Q →* J := QuotientGroup.lift Q ρ hQker with hρbdef
  have hρbs : Function.Surjective ρb := by
    intro φ
    obtain ⟨x, rfl⟩ := hρs φ
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker_ne : ρb.ker ≠ ⊤ := by
    intro htop
    apply hJ2
    intro φ
    obtain ⟨y, rfl⟩ := hρbs φ
    exact ⟨0, by rw [pow_zero, pow_one]; exact (MonoidHom.mem_ker).mp (htop ▸ Subgroup.mem_top y)⟩
  have : Group.IsPerfect (X ⧸ Q) := hq.1
  have hZ : ρb.ker ≤ Subgroup.center (X ⧸ Q) := le_center_of_normal_829 hq ρb.ker hker_ne
  have hker2 : IsPGroup 2 ↥ρb.ker :=
    CFSG.Quasithin.isPGroup_two_ker_of_cyclic_odd_sylow ρb hρbs hZ hcyc
  have hC2 : ∀ x : X, ρ x = 1 → ∃ m : ℕ, x ^ 2 ^ m = 1 := by
    intro x hx
    have hxk : (QuotientGroup.mk x : X ⧸ Q) ∈ ρb.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    obtain ⟨a, ha⟩ := hker2 ⟨_, hxk⟩
    have ha' : (QuotientGroup.mk (x ^ 2 ^ a) : X ⧸ Q) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact congrArg Subtype.val ha
    have hxQ : x ^ 2 ^ a ∈ Q := (QuotientGroup.eq_one_iff _).mp ha'
    obtain ⟨b, hb⟩ := hQ2 ⟨_, hxQ⟩
    refine ⟨a + b, ?_⟩
    have hb' : (x ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_add, pow_mul, hb']
  refine ⟨fun x => ?_, fun p hp hp2 hpJ => ?_⟩
  · obtain ⟨m, hm⟩ := hC2 x (MonoidHom.mem_ker.mp x.2)
    exact ⟨m, Subtype.ext (by rw [Subgroup.coe_pow, hm, Subgroup.coe_one])⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨θ, hθ⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  obtain ⟨l, hl⟩ := hρs θ
  obtain ⟨m, hm⟩ := hC2 (l ^ p) (by rw [map_pow, hl, ← hθ, pow_orderOf_eq_one])
  refine ⟨l ^ 2 ^ m, by rw [← pow_mul, mul_comm, pow_mul, hm], fun h1 => ?_⟩
  rw [map_pow, hl] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hθ] at h2
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
  exact hp2 this

theorem exists_pow_three_not_mem_centralizer_of_gl32 {X U : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X))
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU8 : Nat.card U = 8)
    (hsurj : ∀ φ : MulAut ↥U, ∃ x ∈ X, ∀ u : ↥U, ((φ u : ↥U) : G) = x * u * x⁻¹) :
    ∃ f ∈ X, f ^ 3 = 1 ∧ f ∉ Subgroup.centralizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥U) (p := 2)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2))
    (fun a => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hU2 a a.2))
    (n := 3) (by rw [hU8]; norm_num)
  set J := MulAut ↥U
  have hJc : Nat.card J = 168 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_succ]
  have : IsSimpleGroup J := by
    have := isSimpleGroup_GL32_829
    exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).isSimpleGroup
  have hJ2 : ¬ IsPGroup 2 J := by
    intro h2
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 h2
    rw [hJc] at hm
    have h3 : 3 ∣ 2 ^ m := hm ▸ (by norm_num : 3 ∣ 168)
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  set ρ : ↥X →* J := (conjAct U).comp (Subgroup.inclusion hXU) with hρdef
  have hρ : ∀ (x : ↥X) (u : ↥U), ((ρ x u : ↥U) : G) = (x : G) * u * (x : G)⁻¹ := fun x u =>
    CFSG.QuasithinUnique.Setup.coe_conjAct_apply (Subgroup.inclusion hXU x) u
  have hρs : Function.Surjective ρ := by
    intro φ
    obtain ⟨x, hx, hφ⟩ := hsurj φ
    refine ⟨⟨x, hx⟩, MulEquiv.ext fun u => Subtype.ext ?_⟩
    rw [hρ]
    exact (hφ u).symm
  obtain ⟨-, hf⟩ := isPGroup_ker_and_exists_pow_prime_829 hq ρ hρs hJ2
    fun r _ hr2 _ P => isCyclic_sylow_of_card_dvd (by rw [hJc]) not_sq_dvd_168 hr2 P
  obtain ⟨f, hf3, hfρ⟩ := hf 3 Nat.prime_three (by norm_num) (by rw [hJc]; norm_num)
  refine ⟨(f : G), f.2, by rw [← Subgroup.coe_pow, hf3, Subgroup.coe_one], fun hc => hfρ ?_⟩
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [hρ, ← Subgroup.mem_centralizer_iff.mp hc u u.2, mul_inv_cancel_right]
  rfl

omit [Finite G] in
theorem hsurj_of_autSub_eq_top_829 {V U X : Subgroup G} [IsMulCommutative ↥V] (hUV : U ≤ V)
    (htop : autSub (autOn X V) (U.subgroupOf V) = ⊤) :
    ∀ φ : MulAut ↥U, ∃ x ∈ X, ∀ u : ↥U, ((φ u : ↥U) : G) = x * u * x⁻¹ := by
  intro φ
  let e : ↥(U.subgroupOf V) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUV
  let ψ : MulAut ↥(U.subgroupOf V) := (e.trans φ).trans e.symm
  have hψ : ψ ∈ autSub (autOn X V) (U.subgroupOf V) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hgψ⟩ := mem_autSub.mp hψ
  obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
  have hbX : (b : G) ∈ X := Subgroup.mem_subgroupOf.mp hb
  refine ⟨b, hbX, fun u => ?_⟩
  have h1 := congrArg (fun φ' : MulAut ↥(U.subgroupOf V) =>
    (((φ' (e.symm u) : ↥(U.subgroupOf V)) : ↥V) : G)) hgψ
  have h2 : (((resHom (U.subgroupOf V) g (e.symm u) : ↥(U.subgroupOf V)) : ↥V) : G) =
      b * u * (b : G)⁻¹ := by
    rw [resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    rfl
  have h3 : (((ψ (e.symm u) : ↥(U.subgroupOf V)) : ↥V) : G) = ((φ u : ↥U) : G) := by
    show (((e.symm (φ (e (e.symm u))) : ↥(U.subgroupOf V)) : ↥V) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  exact (h2.symm.trans (h1.trans h3)).symm

theorem exists_f_cocode_829 (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (h827 : Step827)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hmod : StmtFSUModule)
    (h711n : Stmt7_1_1_normal) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) (hcoc : Row711M24Cocode T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k)
    (hC5 : Concl825 T L I h k) :
    ∃ f ∈ ch82LU L (ch82U (fsuV T I) h), f ^ 3 = 1 ∧
      f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, -, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, hcoc'⟩ :=
    lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  set U := ch82U (fsuV T I) h with hUdef
  have hUV : U ≤ fsuV T I := inf_le_left
  have hU2 : IsPGroup 2 ↥U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ (hUV x.2))⟩
  have hLUU : ch82LU L U ≤ Subgroup.normalizer (U : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  obtain ⟨K, hK, hLUK, hKn⟩ := exists_k_828 h37 h38 h39 hyp hU2 hU1 hTU hLUU hfam hLUT
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  have hfam' : ch82LU L U ∈ cComp (ch82LU L U ⊔ T) := hfam
  have hKeq : K = ch82LU L U :=
    eq_of_autSub_eq_top_828 (V := fsuV T I) hUV hfam' hLUK hK hKn hS hq hLUC (hcoc' hcoc)
  subst hKeq
  have hU8 : Nat.card U = 8 := by
    have hrk : rk ↥U = 3 := (hC5.2.2.2.2.2.2.1 hcoc).2.2.2
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hn3 : n = 3 := by
      rw [← hrk]
      unfold rk
      rw [hn, padicValNat.prime_pow]
    rw [hn, hn3]
    norm_num
  exact exists_pow_three_not_mem_centralizer_of_gl32 hLUU hq
    (fun a ha b hb => hc.is_comm.comm ⟨a, hUV ha⟩ ⟨b, hUV hb⟩ |> congrArg Subtype.val)
    (fun u hu => hV.2 u (hUV hu)) hU8 (hsurj_of_autSub_eq_top_829 hUV (hcoc' hcoc))

end L829F3

end CFSG.Quasithin.H13
