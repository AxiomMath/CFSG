module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.H13.U4V

open scoped IsMulCommutative

@[expose] def NSSecThree (G : Type) [Group G] : Prop :=
  ∀ (L : Subgroup G) (N : Subgroup ↥L) [N.Normal], IsSimpleGroup (↥L ⧸ N) →
    (∃ x y : ↥L ⧸ N, x * y ≠ y * x) → 3 ∣ Nat.card (↥L ⧸ N)

section Closure

variable {G G' : Type} [Group G] [Group G']

theorem NSSecThree.three_dvd (h : NSSecThree G') (L : Subgroup G') {S : Type} [Group S]
    (ψ : ↥L →* S) (hψ : Function.Surjective ψ) (hs : IsSimpleGroup S)
    (hnc : ∃ x y : S, x * y ≠ y * x) : 3 ∣ Nat.card S := by
  let e : (↥L ⧸ ψ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hs' : IsSimpleGroup (↥L ⧸ ψ.ker) := e.isSimpleGroup
  have hnc' : ∃ x y : ↥L ⧸ ψ.ker, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    have h1 := congrArg e hc
    simpa using h1
  have h3 := h L ψ.ker hs' hnc'
  rwa [Nat.card_congr e.toEquiv] at h3

theorem NSSecThree.of_injective (f : G →* G') (hf : Function.Injective f) (h : NSSecThree G') :
    NSSecThree G := by
  intro L N _ hs hnc
  let e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  exact h.three_dvd (L.map f) ((QuotientGroup.mk' N).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp e.symm.surjective) hs hnc

theorem NSSecThree.of_mulEquiv (e : G ≃* G') (h : NSSecThree G') : NSSecThree G :=
  h.of_injective e.toMonoidHom e.injective

theorem NSSecThree.of_ker [Finite G] (f : G →* G') (hk : IsPGroup 2 f.ker) (h : NSSecThree G') :
    NSSecThree G := by
  intro L N _ hs hnc
  set fL : ↥L →* G' := f.comp L.subtype with hfL
  set π := QuotientGroup.mk' N with hπ
  have hM : fL.ker ≤ N := by
    have hn : (fL.ker.map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fL.ker.map π) with hbot | htop
    · intro x hx
      have h1 : π x ∈ fL.ker.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have h2 : IsPGroup 2 (↥L ⧸ N) := by
        intro s
        have hs' : s ∈ fL.ker.map π := by
          rw [htop]
          trivial
        obtain ⟨x, hx, rfl⟩ := hs'
        have hxk : ((x : ↥L) : G) ∈ f.ker := hx
        obtain ⟨k, hk'⟩ := hk ⟨_, hxk⟩
        refine ⟨k, ?_⟩
        have hx1 : x ^ 2 ^ k = 1 := by
          apply Subtype.ext
          have h3 := congrArg Subtype.val hk'
          simpa using h3
        rw [← map_pow, hx1, map_one]
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (InternalSec.commute_of_isPGroup_two h2 a b)
  let g : ↥L →* ↥(L.map f) := fL.codRestrict (L.map f) fun x => ⟨x, x.2, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgk : g.ker ≤ N := by
    intro x hx
    apply hM
    have h1 : ((g x : ↥(L.map f)) : G') = 1 := by
      rw [MonoidHom.mem_ker.mp hx]
      rfl
    exact h1
  let e : (↥L ⧸ g.ker) ≃* ↥(L.map f) := QuotientGroup.quotientKerEquivOfSurjective g hg
  let ψ : ↥(L.map f) →* ↥L ⧸ N :=
    (QuotientGroup.map g.ker N (MonoidHom.id _) hgk).comp e.symm.toMonoidHom
  refine h.three_dvd (L.map f) ψ ?_ hs hnc
  intro s
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N s
  refine ⟨g x, ?_⟩
  have h1 : e.symm (g x) = (QuotientGroup.mk x : ↥L ⧸ g.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.map g.ker N (MonoidHom.id _) hgk (e.symm (g x)) = _
  rw [h1]
  rfl

theorem NSSecThree.of_commutator_le (H : Subgroup G) (hH : commutator G ≤ H)
    (h : NSSecThree ↥H) : NSSecThree G := by
  intro L N _ hs hnc
  set π := QuotientGroup.mk' N with hπ
  have hHn : H.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : g * x * g⁻¹ * x⁻¹ ∈ H :=
      hH (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
    have h2 := H.mul_mem h1 hx
    simpa using h2
  set LH : Subgroup ↥L := H.comap L.subtype with hLH
  have hLHn : LH.Normal := Subgroup.Normal.comap hHn L.subtype
  have hn : (LH.map π).Normal := Subgroup.Normal.map hLHn π (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (LH.map π) with hbot | htop
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
    apply hxy
    have hc : a * b * a⁻¹ * b⁻¹ ∈ LH :=
      hH (Subgroup.commutator_mem_commutator (Subgroup.mem_top (a : G))
        (Subgroup.mem_top (b : G)))
    have h1 : π (a * b * a⁻¹ * b⁻¹) ∈ LH.map π := ⟨_, hc, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π a * π b = π b * π a := by
      calc π a * π b = (π a * π b * (π a)⁻¹ * (π b)⁻¹) * (π b * π a) := by group
        _ = π b * π a := by rw [h1, one_mul]
    exact h2
  · set L₁ : Subgroup ↥H := L.subgroupOf H with hL₁
    let ι : ↥L₁ →* ↥L :=
      { toFun := fun x => ⟨((x : ↥H) : G), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine h.three_dvd L₁ (π.comp ι) ?_ hs hnc
    intro s
    have hs' : s ∈ LH.map π := by
      rw [htop]
      trivial
    obtain ⟨l, hl, rfl⟩ := hs'
    exact ⟨⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.mpr l.2⟩, rfl⟩

end Closure

section Orders

variable {S : Type} [Group S] [Finite S]

theorem three_dvd_of_card_dvd (hs : IsSimpleGroup S) (hnc : ∃ x y : S, x * y ≠ y * x) {a b : ℕ}
    (hd : Nat.card S ∣ 2 ^ a * 3 ^ b) : 3 ∣ Nat.card S := by
  by_contra h3
  have hcop : Nat.Coprime (Nat.card S) (3 ^ b) :=
    Nat.Coprime.pow_right b ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr h3)))
  have h2 : Nat.card S ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hp : IsPGroup 2 S := IsPGroup.of_card hk
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (InternalSec.commute_of_isPGroup_two hp x y)

theorem card_quotient_of_isSimpleGroup {L : Type} [Group L] [IsSimpleGroup L] (N : Subgroup L)
    [N.Normal] (hs : IsSimpleGroup (L ⧸ N)) : Nat.card (L ⧸ N) = Nat.card L := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · subst hbot
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  · exfalso
    subst htop
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (L ⧸ (⊤ : Subgroup L))).exists_pair_ne
    apply hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [QuotientGroup.eq]
        trivial

end Orders

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_psl2_of_charTwo :
    Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 1 := by
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.card_bot]
  rw [hc, mul_one] at h1
  rw [← CFSG.GorensteinWalter.sl2_card_formula F, h1]

theorem three_dvd_card_mul (m : ℕ) : 3 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h := Nat.sub_dvd_pow_sub_pow 4 1 m
  rw [one_pow] at h
  rw [← pow_mul, mul_comm, pow_mul]
  exact h

end SL2

section Dickson

theorem false_of_comm {L : Type} [Group L] {N : Subgroup L} [N.Normal]
    (hc : ∀ a b : L, a * b = b * a) (hnc : ∃ x y : L ⧸ N, x * y ≠ y * x) : False := by
  obtain ⟨x, y, hxy⟩ := hnc
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
  apply hxy
  rw [← map_mul, ← map_mul, hc a b]

theorem false_of_isSolvable {L : Type} [Group L] [Group.IsSolvable L] {N : Subgroup L} [N.Normal]
    (hs : IsSimpleGroup (L ⧸ N)) (hnc : ∃ x y : L ⧸ N, x * y ≠ y * x) : False := by
  have : Group.IsSolvable (L ⧸ N) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)

theorem three_dvd_of_card_eq {L : Type} [Group L] [Finite L] {N : Subgroup L} [N.Normal]
    (hs : IsSimpleGroup (L ⧸ N)) (hnc : ∃ x y : L ⧸ N, x * y ≠ y * x) {a b : ℕ}
    (hL : Nat.card L = 2 ^ a * 3 ^ b) : 3 ∣ Nat.card (L ⧸ N) := by
  refine three_dvd_of_card_dvd hs hnc (a := a) (b := b) ?_
  rw [← hL]
  exact Subgroup.card_quotient_dvd_card N

theorem toPGL_bijective {F : Type} [Field F] [Finite F] [CharP F 2] :
    Function.Bijective (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F →* Matrix.ProjGenLinGroup (Fin 2) F) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 2) F →
      Matrix.ProjGenLinGroup (Fin 2) F) Matrix.ProjGenLinGroup.mk_surjective
  have hcard : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) ≤
      Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := by
    rw [card_psl2_of_charTwo]
    exact (CFSG.GorensteinWalter.pgl2_card_formula F).le
  exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.bijective_of_nat_card_le hcard

theorem nsSecThree_psl2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    NSSecThree (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
  intro L N _ hs hnc
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF L with
    ⟨-, -, -, hel⟩ | ⟨-, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨-, -, -, -, -, -, E, C, hEn, hE, -, hC, -, -, hEC, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    exact (false_of_comm (fun a b => hel.toIsMulCommutative.is_comm.comm a b) hnc).elim
  ·
    exact (false_of_comm (fun a b => (IsCyclic.commGroup (α := ↥L)).mul_comm a b) hnc).elim
  ·
    have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact (false_of_isSolvable hs hnc).elim
  ·
    refine three_dvd_of_card_eq hs hnc (a := 2) (b := 1) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  ·
    refine three_dvd_of_card_eq hs hnc (a := 3) (b := 1) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  ·
    have : IsSimpleGroup ↥L := e.isSimpleGroup
    rw [card_quotient_of_isSimpleGroup N hs, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
    decide
  ·
    exfalso
    set π := QuotientGroup.mk' N with hπ
    have hEb : (E.map π).Normal := Subgroup.Normal.map hEn π (QuotientGroup.mk'_surjective N)
    have himg : ∀ A : Subgroup ↥L, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A.map π = ⊤ → False := by
      intro A hA htop
      obtain ⟨x, y, hxy⟩ := hnc
      have hx : x ∈ A.map π := by
        rw [htop]
        trivial
      have hy : y ∈ A.map π := by
        rw [htop]
        trivial
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      apply hxy
      rw [← map_mul, ← map_mul, hA a ha b hb]
    have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map π) with hbot | htop
    · have hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val ((IsCyclic.commGroup (α := ↥C)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
      refine himg C hCc ?_
      have h1 := congrArg (Subgroup.map π) hEC
      rw [Subgroup.map_sup, hbot, bot_sup_eq, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)] at h1
      exact h1
    · exact himg E hEc htop
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hm)
    have hcard : Nat.card ↥L = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_psl2_of_charTwo, GaloisField.card 2 m hm0]
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      exact three_dvd_of_card_eq hs hnc (a := 1) (b := 1) (by rw [hcard]; norm_num)
    · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
        rw [GaloisField.card 2 m hm0]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
      have : IsSimpleGroup ↥L := e.isSimpleGroup
      rw [card_quotient_of_isSimpleGroup N hs, hcard]
      exact three_dvd_card_mul m
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    have hcard : Nat.card ↥L = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
        GaloisField.card 2 m hm0]
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      exact three_dvd_of_card_eq hs hnc (a := 1) (b := 1) (by rw [hcard]; norm_num)
    · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
        rw [GaloisField.card 2 m hm0]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
      let f : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 m) ≃*
          Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m) :=
        MulEquiv.ofBijective _ toPGL_bijective
      have : IsSimpleGroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) :=
        f.symm.isSimpleGroup
      have : IsSimpleGroup ↥L := e.isSimpleGroup
      rw [card_quotient_of_isSimpleGroup N hs, hcard]
      exact three_dvd_card_mul m

theorem nsSecThree_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    NSSecThree (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hZ := CFSG.Walter.sl2_center_eq_bot_of_charTwo (K := F)
  let e : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact nsSecThree_psl2.of_mulEquiv e.symm

end Dickson

end CFSG.Quasithin.H13.U4V
