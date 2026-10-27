module

public import CFSG.Walter.Cited.SuzukiHyp
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.Walter.Suzuki

open scoped MatrixGroups
open CFSG.GorensteinWalter

theorem isMulCommutative_of_map_le {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {K : Subgroup G} {A : Subgroup H} (hA : IsMulCommutative A)
    (hKA : K.map f ≤ A) : IsMulCommutative K := by
  refine ⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩
  have ha : f a ∈ A := hKA ⟨a, a.2, rfl⟩
  have hb : f b ∈ A := hKA ⟨b, b.2, rfl⟩
  have := congrArg Subtype.val (hA.is_comm.comm ⟨f a, ha⟩ ⟨f b, hb⟩)
  simpa using this

theorem eq_one_of_central_of_card_sixty {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) {z : X} (hz : ∀ y : X, z * y = y * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_center_iff.mpr fun y => (hz y).symm)
  · exfalso
    let : CommGroup X :=
      { (inferInstance : Group X) with
        mul_comm := fun a b => Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := X)
    rw [hX] at hp
    norm_num at hp

variable {M : Type} [Group M] [Finite M]

theorem exists_normal_of_card_three (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f) (h3 : p ^ f = 3)
    (L : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)) (hLn : L.Normal) (e : L ≃* PSL(2, K)) :
    ∃ T : Subgroup (M ⧸ CFSG.pPrimeCore 2 M), T.Normal ∧ Nat.card T = 4 := by
  have hpp : IsOddPrimePower (Nat.card K) := ⟨p, f, Fact.out, hp, hf, hK⟩
  have hL12 : Nat.card L = 12 := by
    rw [Nat.card_congr e.toEquiv, card_psl2_of_card K hpp (hK.trans h3)]
    norm_num
  have hsub : Subsingleton (Sylow 2 L) := by
    refine subsingleton_sylow_two_of_card_twelve hL12 fun u hu => ?_
    have hmap := CFSG.centralizer_singleton_map e u
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
    exact card_centralizer_of_card_three K hK hp hf h3 (by rw [MulEquiv.orderOf_eq, hu])
  obtain ⟨P⟩ : Nonempty (Sylow 2 L) := inferInstance
  refine ⟨(P : Subgroup L).map L.subtype, ConjAct.normal_of_characteristic_of_normal, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, P.card_eq_multiplicity, hL12,
    factorization_two_twelve]
  norm_num

namespace Hyp

variable (h : Hyp M)
include h

theorem hasDihedralSylowTwo : HasDihedralSylowTwo M := by
  intro S
  have := h.klein S
  exact ⟨1, le_rfl, by rw [pow_one]; exact IsKleinFour.nonempty_mulEquiv⟩

theorem not_alternatingGroup_seven :
    ¬ Nonempty ((M ⧸ CFSG.pPrimeCore 2 M) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  apply h.not_eight_dvd_card_quotient
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem not_pgl2 (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)) (e : L ≃* PGL2 K) : False := by
  apply h.not_eight_dvd_card_quotient
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p, n, -, hp, -, hq⟩ := hK
    rw [hq]
    exact hp.pow
  have h8 : 8 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
    exact Dvd.dvd.mul_left (eight_dvd_sq_sub_one hodd) _
  exact h8.trans (Subgroup.card_subgroup_dvd_card L)

theorem card_eq_three_or_five (K : Type) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (L : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)) (e : L ≃* PSL(2, K)) :
    p ^ f = 3 ∨ p ^ f = 5 := by
  have hpp : IsOddPrimePower (Nat.card K) := ⟨p, f, Fact.out, hp, hf, hK⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_psl2 K hpp)
  set t' : L := e.symm t
  have ht' : orderOf (t' : M ⧸ CFSG.pPrimeCore 2 M) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hCQ := h.isMulCommutative_centralizer_quotient ht'
  have hCL : IsMulCommutative (Subgroup.centralizer ({t'} : Set L)) := by
    refine isMulCommutative_of_map_le L.subtype_injective hCQ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))
  have hmap := CFSG.centralizer_singleton_map e t'
  rw [show e t' = t from e.apply_symm_apply t] at hmap
  have hCP : IsMulCommutative (Subgroup.centralizer ({t} : Set PSL(2, K))) := by
    rw [← hmap]
    infer_instance
  exact eq_three_or_five_of_isMulCommutative K hK hp hf ht hCP

theorem eq_top_of_card_five (K : Type) [Field K] [Finite K] (hK5 : Nat.card K = 5)
    (L : Subgroup (M ⧸ CFSG.pPrimeCore 2 M)) (hLn : L.Normal) (hLi : Odd L.index)
    (e : L ≃* PSL(2, K)) : L = ⊤ := by
  set Q := M ⧸ CFSG.pPrimeCore 2 M
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpp : IsOddPrimePower (Nat.card K) :=
    ⟨5, 1, Nat.prime_five, by decide, le_rfl, by rw [hK5]; norm_num⟩
  have hL60 : Nat.card L = 60 := by
    rw [Nat.card_congr e.toEquiv, card_psl2_of_card K hpp hK5]
    norm_num
  have : IsSimpleGroup PSL(2, K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK5]; norm_num)
  have hLs : IsSimpleGroup L := e.isSimpleGroup
  set C := Subgroup.centralizer (L : Set Q) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCodd : Odd (Nat.card C) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hev.two_dvd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (by rw [hL60]; norm_num)
    have hc' : orderOf (c : Q) = 2 := by rw [Subgroup.orderOf_coe, hc]
    have hu' : orderOf (u : Q) = 2 := by rw [Subgroup.orderOf_coe, hu]
    obtain ⟨g, hg⟩ := isConj_iff.mp (h.isConj_quotient hc' hu')
    have huC : (u : Q) ∈ C := hg ▸ hCn.conj_mem _ c.2 g
    have hu1 : u = 1 := eq_one_of_central_of_card_sixty hL60 fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp huC y y.2).symm)
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hCbot : C = ⊥ := eq_bot_of_odd_quotient hCn hCodd
  have hinj : Function.Injective (MulAut.conjNormal (H := L) : Q →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgC : g ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro l hl
      have := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : Q)) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc l * g = (g * l * g⁻¹) * g := by rw [this]
        _ = g * l := by group
    rw [hCbot] at hgC
    exact hgC
  have hQle : Nat.card Q ≤ 120 := by
    calc Nat.card Q ≤ Nat.card (MulAut L) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card (MulAut PSL(2, K)) := Nat.card_congr (MulAut.congr e).toEquiv
      _ ≤ 120 := card_mulAut_psl2_le_of_card_five K hK5
  have hQ : Nat.card L * L.index = Nat.card Q := L.card_mul_index
  rw [hL60] at hQ
  have hi : L.index = 1 := by
    obtain ⟨k, hk⟩ := hLi
    omega
  exact Subgroup.index_eq_one.mp hi

theorem quotient_cases :
    (∃ T : Subgroup (M ⧸ CFSG.pPrimeCore 2 M), T.Normal ∧ Nat.card T = 4) ∨
      (IsSimpleGroup (M ⧸ CFSG.pPrimeCore 2 M) ∧ Nat.card (M ⧸ CFSG.pPrimeCore 2 M) = 60) := by
  set Q := M ⧸ CFSG.pPrimeCore 2 M
  rcases gorensteinWalter M h.hasDihedralSylowTwo with ⟨-, h2⟩ | ⟨-, e⟩ |
    ⟨-, K, hK, L, hLn, hLi, hLmodel⟩
  ·
    left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have hk2 := h.factorization_two_quotient
    rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hk2
    refine ⟨⊤, inferInstance, ?_⟩
    rw [Subgroup.card_top]
    change Nat.card Q = 4
    rw [hk, hk2]
    norm_num
  · exact absurd e h.not_alternatingGroup_seven
  · rcases hLmodel with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨p, f, hp, hpodd, hf, hq⟩ := hK
      have : Fact p.Prime := ⟨hp⟩
      rcases h.card_eq_three_or_five K hq hpodd hf L e with h3 | h5
      · exact Or.inl (exists_normal_of_card_three K hq hpodd hf h3 L hLn e)
      · right
        have hLtop := h.eq_top_of_card_five K (hq.trans h5) L hLn hLi e
        let e' : Q ≃* PSL(2, K) :=
          (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans e
        have : IsSimpleGroup PSL(2, K) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hq, h5]; norm_num)
        refine ⟨e'.isSimpleGroup, ?_⟩
        rw [Nat.card_congr e'.toEquiv, card_psl2_of_card K ⟨p, f, hp, hpodd, hf, hq⟩
          (hq.trans h5)]
        norm_num
    · obtain ⟨e⟩ := he
      exact (h.not_pgl2 K hK L e).elim

end Hyp

end CFSG.Walter.Suzuki
