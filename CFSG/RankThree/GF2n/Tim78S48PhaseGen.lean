module

public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.RankThree.GF2n.Tim78Frobenius
import CFSG.RankThree.GF2n.Tim78Counting
import CFSG.RankThree.GF2n.Tim78NaturalModule
import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.CGT.Timmesfeld75.L2Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open CFSG.RankThree.GF2n
open Matrix
open scoped MatrixGroups

section Acting

variable {Γ V : Type} [Group Γ] [Group V]

def fixedSub (ρ : Γ →* MulAut V) (A : Subgroup Γ) : Subgroup V where
  carrier := {v | ∀ a ∈ A, ρ a v = v}
  mul_mem' := by
    intro x y hx hy a ha
    rw [map_mul, hx a ha, hy a ha]
  one_mem' := fun a _ => map_one _
  inv_mem' := by
    intro x hx a ha
    rw [map_inv, hx a ha]

theorem mem_fixedSub {ρ : Γ →* MulAut V} {A : Subgroup Γ} {v : V} :
    v ∈ fixedSub ρ A ↔ ∀ a ∈ A, ρ a v = v := Iff.rfl

theorem inr_mul_inl (ρ : Γ →* MulAut V) (a : Γ) (v : V) :
    (SemidirectProduct.inr a : V ⋊[ρ] Γ) * SemidirectProduct.inl v =
      SemidirectProduct.inl (ρ a v) * SemidirectProduct.inr a := by
  have h := SemidirectProduct.inl_aut (φ := ρ) a v
  rw [h, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem inr_comm_inl_iff (ρ : Γ →* MulAut V) (a : Γ) (v : V) :
    (SemidirectProduct.inr a : V ⋊[ρ] Γ) * SemidirectProduct.inl v =
      SemidirectProduct.inl v * SemidirectProduct.inr a ↔ ρ a v = v := by
  rw [inr_mul_inl, mul_left_inj, SemidirectProduct.inl_inj]

theorem tim78_2_4_acting [Finite Γ] [Finite V] (ρ : Γ →* MulAut V)
    (hVc : ∀ a b : V, a * b = b * a) (hV2 : ∀ a : V, a * a = 1)
    {L K : Subgroup Γ} {n : ℕ} (hLcard : Nat.card L = 2 ^ n)
    (hKcard : Nat.card K = Nat.card L - 1) (hKL : K ≤ Subgroup.normalizer (L : Set Γ))
    (hfrob : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ L, k * x * k⁻¹ = x → x = 1)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hA : ∃ A : Subgroup Γ, A ≤ L ∧ A ≠ ⊥ ∧
      Nat.card V ≤ Nat.card A * Nat.card (fixedSub ρ A)) :
    Nat.card V ≤ Nat.card L * Nat.card (fixedSub ρ L) := by
  classical
  haveI : Finite (V ⋊[ρ] Γ) :=
    Finite.of_equiv _ (SemidirectProduct.equivProd (N := V) (G := Γ) (φ := ρ)).symm
  set V' : Subgroup (V ⋊[ρ] Γ) := (⊤ : Subgroup V).map SemidirectProduct.inl with hV'
  set L' : Subgroup (V ⋊[ρ] Γ) := L.map SemidirectProduct.inr with hL'
  set K' : Subgroup (V ⋊[ρ] Γ) := K.map SemidirectProduct.inr with hK'
  have hcent : ∀ A : Subgroup Γ, cent V' (A.map SemidirectProduct.inr) =
      (fixedSub ρ A).map SemidirectProduct.inl := by
    intro A
    ext x
    simp only [cent, Subgroup.mem_inf, hV', Subgroup.mem_map, Subgroup.mem_top, true_and,
      Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨v, rfl⟩, hx⟩
      refine ⟨v, fun a ha => ?_, rfl⟩
      exact (inr_comm_inl_iff ρ a v).mp (hx (SemidirectProduct.inr a) ⟨a, ha, rfl⟩)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact (inr_comm_inl_iff ρ a v).mpr (hv a ha)
  have hcardV' : Nat.card V' = Nat.card V := by
    rw [hV', Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Subgroup.card_top]
  have hcardL' : Nat.card L' = Nat.card L := by
    rw [hL', Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
  have hcardK' : Nat.card K' = Nat.card K := by
    rw [hK', Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
  have hcentcard : ∀ A : Subgroup Γ, Nat.card (cent V' (A.map SemidirectProduct.inr)) =
      Nat.card (fixedSub ρ A) := by
    intro A
    rw [hcent, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  have hVe : Assembly.IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', -, ha⟩ := a.2
      obtain ⟨b', -, hb⟩ := b.2
      apply Subtype.ext
      show (a : V ⋊[ρ] Γ) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hVc]
    · obtain ⟨x', -, hx'⟩ := hx
      rw [← hx', ← map_pow]
      have : x' ^ 2 = 1 := by rw [sq]; exact hV2 x'
      rw [this, map_one]
  have key := tim78_2_4 (L := L') (K := K') (V := V') (n := n) (by rw [hcardL']; exact hLcard)
    (by rw [hcardK', hcardL']; exact hKcard) ?_ ?_ ?_ hVe ?_ ?_
  · have hc : Nat.card (cent V' L') = Nat.card (fixedSub ρ L) := hcentcard L
    rw [hcardV', hcardL', hc] at key
    exact key
  ·
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨k * l * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKL hk) l).mp hl, rfl⟩
  ·
    rintro _ ⟨k, hk, rfl⟩ hk1 _ ⟨l, hl, rfl⟩ hkl
    have hk1' : k ≠ 1 := fun h => hk1 (by rw [h, map_one])
    rw [← map_inv, ← map_mul, ← map_mul] at hkl
    have := hfrob k hk hk1' l hl (SemidirectProduct.inr_injective hkl)
    rw [this, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hKc a ha b hb]
  ·
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, -, rfl⟩ := hx
    rw [← map_inv, ← SemidirectProduct.inl_aut]
    exact ⟨ρ k v, trivial, rfl⟩
  · obtain ⟨A, hAL, hA1, hAc⟩ := hA
    refine ⟨A.map SemidirectProduct.inr, Subgroup.map_mono hAL, ?_, ?_⟩
    · intro h
      apply hA1
      rw [eq_bot_iff]
      intro a ha
      have : (SemidirectProduct.inr a : V ⋊[ρ] Γ) ∈ A.map SemidirectProduct.inr := ⟨a, ha, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact SemidirectProduct.inr_injective (this.trans (map_one _).symm)
    · rw [hcardV', hcentcard A, Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
      exact hAc

theorem tim78_2_5_sub [Finite Γ] {Ω H : Subgroup Γ}
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHodd : Odd (Nat.card H))
    (hΩe : Assembly.IsElemAbelian 2 Ω) (hΩnt : Ω ≠ ⊥)
    (hHΩ : H ≤ Subgroup.normalizer (Ω : Set Γ))
    (hfaith : ∀ h ∈ H, (∀ x ∈ Ω, h * x * h⁻¹ = x) → h = 1) :
    Nat.card H < Nat.card Ω - 1 ∨
      (Nat.card H = Nat.card Ω - 1 ∧
        ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ 1 → y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Ω := (Subgroup.nontrivial_iff_ne_bot Ω).mpr hΩnt
  let φ : H →* MulAut Ω := Ω.normalizerMonoidHom.comp (Subgroup.inclusion hHΩ)
  have hφ : ∀ (h : H) (z : Ω), ((φ h z : Ω) : Γ) = h * z * (h : Γ)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    apply Subtype.ext
    refine hfaith h h.2 fun z hz => ?_
    have := congrArg (fun f : MulAut Ω => ((f ⟨z, hz⟩ : Ω) : Γ)) hh
    rw [hφ] at this
    exact this
  have hKcard : Nat.card φ.range = Nat.card H :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hKc : ∀ a ∈ φ.range, ∀ b ∈ φ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hHc a a.2 b b.2))
  have hPc : ∀ a b : Ω, a * b = b * a := fun a b => hΩe.1.is_comm.comm a b
  have hPp : ∀ a : Ω, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hΩe.2 a a.2)
  have hKp : ¬ 2 ∣ Nat.card φ.range := by
    rw [hKcard, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hHodd
  rcases tim78_2_5 hPc hPp φ.range hKc hKp with hlt | ⟨h1, htr⟩
  · exact Or.inl (hKcard ▸ hlt)
  · refine Or.inr ⟨hKcard ▸ h1, fun x hx y hy hx1 hy1 => ?_⟩
    obtain ⟨⟨k, ⟨h, rfl⟩⟩, hk, -⟩ := htr ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
    exact ⟨h, h.2, congrArg Subtype.val hk⟩


end Acting

theorem exists_conj_utri_ltri (f : ℕ) (hf : f ≠ 0) {P₁ P₂ : Subgroup SL(2, GaloisField 2 f)}
    (h1 : IsPGroup 2 P₁) (h2 : IsPGroup 2 P₂) (c1 : Nat.card P₁ = 2 ^ f)
    (c2 : Nat.card P₂ = 2 ^ f) (hne : P₁ ≠ P₂) :
    ∃ c : SL(2, GaloisField 2 f), conjSubgroup c P₁ = utri (GaloisField 2 f) ∧
      conjSubgroup c P₂ = ltri (GaloisField 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := CFSG.RankThree.GF2n.Tim78.card_SL_two_galoisField hf
  have hodd : ∀ P : Subgroup SL(2, GaloisField 2 f), Nat.card P = 2 ^ f → ¬ 2 ∣ P.index := by
    intro P hP hdvd
    have h := Subgroup.index_mul_card P
    rw [hcard, hP] at h
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow hf
    have hpos : 0 < 2 ^ f := by omega
    have h2 : P.index = (2 ^ f) ^ 2 - 1 := by
      have : P.index * 2 ^ f = ((2 ^ f) ^ 2 - 1) * 2 ^ f := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    rw [h2] at hdvd
    have h4 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf) two_ne_zero
    have h5 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ hpos
    omega
  let S₁ : Sylow 2 SL(2, GaloisField 2 f) := IsPGroup.toSylow h1 (hodd P₁ c1)
  let S₂ : Sylow 2 SL(2, GaloisField 2 f) := IsPGroup.toSylow h2 (hodd P₂ c2)
  obtain ⟨a, ha⟩ := exists_conjSubgroup_utri_eq_of_sylow S₁
  obtain ⟨b, hb⟩ := exists_conjSubgroup_utri_eq_of_sylow S₂
  have hS₁ : (S₁ : Subgroup SL(2, GaloisField 2 f)) = P₁ := rfl
  have hS₂ : (S₂ : Subgroup SL(2, GaloisField 2 f)) = P₂ := rfl
  rw [hS₁] at ha
  rw [hS₂] at hb
  have hab : conjSubgroup a (utri (GaloisField 2 f)) ≠ conjSubgroup b (utri (GaloisField 2 f)) := by
    rw [ha, hb]; exact hne
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_normal_form hab
  refine ⟨g, ?_, ?_⟩
  · rw [← ha, conjSubgroup_conjSubgroup]; exact hg1
  · rw [← hb, conjSubgroup_conjSubgroup]; exact hg2

theorem exists_sl2_coords {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal] {f : ℕ}
    (hf : f ≠ 0) (e : Y ⧸ N ≃* PSL(2, GaloisField 2 f)) {S S' : Subgroup Y}
    (hS : IsPGroup 2 S) (hS' : IsPGroup 2 S')
    (hc : Nat.card (S.map (QuotientGroup.mk' N)) = 2 ^ f)
    (hc' : Nat.card (S'.map (QuotientGroup.mk' N)) = 2 ^ f)
    (hne : S.map (QuotientGroup.mk' N) ≠ S'.map (QuotientGroup.mk' N)) :
    ∃ ε : Y →* SL(2, GaloisField 2 f), Function.Surjective ε ∧ ε.ker = N ∧
      S.map ε = utri (GaloisField 2 f) ∧ S'.map ε = ltri (GaloisField 2 f) := by
  classical
  set e₁ : Y ⧸ N ≃* SL(2, GaloisField 2 f) := e.trans pslMulEquivSL with he₁
  set π := QuotientGroup.mk' N with hπ
  have hP₁ : IsPGroup 2 ((S.map π).map e₁.toMonoidHom) := (hS.map π).map e₁.toMonoidHom
  have hP₂ : IsPGroup 2 ((S'.map π).map e₁.toMonoidHom) := (hS'.map π).map e₁.toMonoidHom
  have c₁ : Nat.card ((S.map π).map e₁.toMonoidHom) = 2 ^ f := by
    rw [Subgroup.card_map_of_injective e₁.injective, hc]
  have c₂ : Nat.card ((S'.map π).map e₁.toMonoidHom) = 2 ^ f := by
    rw [Subgroup.card_map_of_injective e₁.injective, hc']
  have hne' : (S.map π).map e₁.toMonoidHom ≠ (S'.map π).map e₁.toMonoidHom := fun h =>
    hne (Subgroup.map_injective e₁.injective h)
  obtain ⟨c, hc1, hc2⟩ := exists_conj_utri_ltri f hf hP₁ hP₂ c₁ c₂ hne'
  refine ⟨(MulAut.conj c).toMonoidHom.comp (e₁.toMonoidHom.comp π), ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj c).surjective.comp (e₁.surjective.comp (QuotientGroup.mk'_surjective N))
  · ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · rw [← hc1, conjSubgroup, Subgroup.map_map, Subgroup.map_map]
    rfl
  · rw [← hc2, conjSubgroup, Subgroup.map_map, Subgroup.map_map]
    rfl

theorem exists_sl2_torus_lift {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : f ≠ 0)
    (ε : Y →* SL(2, GaloisField 2 f)) (hε : Function.Surjective ε) (hN : IsPGroup 2 ε.ker) :
    ∃ K₁ : Subgroup Y, IsCyclic K₁ ∧ Nat.card K₁ = 2 ^ f - 1 ∧
      K₁.map ε = torus (GaloisField 2 f) ∧ K₁ ⊓ ε.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  set Z : Subgroup Y := (torus F).comap ε with hZ
  have hkerZ : ε.ker ≤ Z := fun x hx => by
    rw [hZ, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact (torus F).one_mem
  set N' : Subgroup Z := ε.ker.subgroupOf Z with hN'
  haveI hN'n : N'.Normal := Subgroup.Normal.subgroupOf inferInstance Z
  let ε' : Z →* torus F := (ε.comp Z.subtype).codRestrict (torus F) fun z => z.2
  have hε'ker : ε'.ker = N' := by
    ext z
    simp only [MonoidHom.mem_ker, hN', Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have hε's : Function.Surjective ε' := by
    rintro ⟨t, ht⟩
    obtain ⟨y, rfl⟩ := hε t
    exact ⟨⟨y, ht⟩, rfl⟩
  have hcardT : Nat.card (torus F) = 2 ^ f - 1 := by
    rw [card_torus, hFdef, GaloisField.card 2 f hf]
  have hidx : N'.index = 2 ^ f - 1 := by
    rw [← hε'ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hε's, Subgroup.card_top, hcardT]
  have hN'card : Nat.card N' = Nat.card ε.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerZ).toEquiv
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hN
  have hodd : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hf).mpr even_two) odd_one
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hk, hidx]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = 2 ^ f - 1 := by
    rw [← hidx]; exact (hH.symm.index_eq_card).symm
  have hdisj : Disjoint N' H := hH.disjoint
  let ρ : H →* torus F := ε'.comp H.subtype
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : Z) ∈ N' := by rw [← hε'ker]; exact hx
    have h2 : (x : Z) ∈ N' ⊓ H := ⟨h1, x.2⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hρbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (by rw [hHcard, hcardT])
  let K₁ : Subgroup Y := H.map Z.subtype
  have hK₁card : Nat.card K₁ = 2 ^ f - 1 := by
    rw [Subgroup.card_map_of_injective Z.subtype_injective, hHcard]
  have hHcyc : IsCyclic H := by
    have : IsCyclic (torus F) := isCyclic_torus
    exact isCyclic_of_surjective (MulEquiv.ofBijective ρ hρbij).symm.toMonoidHom
      (MulEquiv.ofBijective ρ hρbij).symm.surjective
  refine ⟨K₁, ?_, hK₁card, ?_, ?_⟩
  · exact isCyclic_of_surjective (H.equivMapOfInjective Z.subtype Z.subtype_injective).toMonoidHom
      (H.equivMapOfInjective Z.subtype Z.subtype_injective).surjective
  · ext g
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact h.2
    · intro hg
      obtain ⟨h, hh⟩ := hρbij.2 ⟨g, hg⟩
      exact ⟨h, ⟨h, h.2, rfl⟩, congrArg Subtype.val hh⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨h, hh, rfl⟩, hker⟩
    have h1 : (h : Z) ∈ N' := Subgroup.mem_subgroupOf.mpr hker
    have h2 : (h : Z) ∈ N' ⊓ H := ⟨h1, hh⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot, h2]
    rfl

theorem card_sup_of_disjoint {V : Type*} [AddCommGroup V] (A B : AddSubgroup V)
    (h : Disjoint A B) :
    Nat.card (A ⊔ B : AddSubgroup V) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : A × B => (⟨(p.1 : V) + p.2, AddSubgroup.add_mem _
      (AddSubgroup.mem_sup_left p.1.2) (AddSubgroup.mem_sup_right p.2.2)⟩ : ↥(A ⊔ B)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : V) + b = a' + b' := congrArg Subtype.val hab
    have h2 : (a : V) - a' = b' - b := by
      have := h1
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    have h3 : ((a : V) - a') ∈ A ⊓ B := ⟨A.sub_mem a.2 a'.2, h2 ▸ B.sub_mem b'.2 b.2⟩
    rw [disjoint_iff.mp h, AddSubgroup.mem_bot, sub_eq_zero] at h3
    have h4 : (b : V) = b' := by
      have := h1
      rw [h3] at this
      exact add_left_cancel this
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem card_sup_of_supIndep {V : Type*} [AddCommGroup V] [DecidableEq (AddSubgroup V)]
    (s : Finset (AddSubgroup V)) (hs : s.SupIndep id) :
    Nat.card (s.sup id : AddSubgroup V) = ∏ W ∈ s, Nat.card W := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs1 : s.SupIndep id := hs.subset (Finset.subset_insert a s)
    have hs2 : Disjoint a (s.sup id) := by
      have := Finset.supIndep_iff_disjoint_erase.mp hs a (Finset.mem_insert_self a s)
      rwa [Finset.erase_insert ha] at this
    rw [Finset.sup_insert, Finset.prod_insert ha, id, card_sup_of_disjoint _ _ hs2, ih hs1]

theorem natural_module_decomp {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Finite V] [DistribMulAction SL(2, F) V]
    (hfix : ∀ v : V, (∀ x : SL(2, F), x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent F, ∀ a' ∈ upperUnipotent F, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {L : AddSubgroup V} (hL : ∀ w ∈ L, ∀ a ∈ upperUnipotent F, a • w = w)
    (hgen : ∀ U : AddSubgroup V, (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) → L ≤ U → U = ⊤) :
    ∃ m : ℕ, Nat.card V = (Nat.card F ^ 2) ^ m ∧
      (m = 1 → ∃ θ : (Fin 2 → F) →+ V, Function.Bijective θ ∧
        ∀ (x : SL(2, F)) (v : Fin 2 → F), θ ((x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x • θ v) := by
  classical
  obtain ⟨s, hs, hsup, hW⟩ := exists_supIndep_natural hfix hquad hL hgen
  have hcard : ∀ W ∈ s, Nat.card W = Nat.card F ^ 2 := by
    intro W hWs
    obtain ⟨-, -, -, θ, hinj, hrange, -⟩ := hW W hWs
    have h1 : Nat.card θ.range = Nat.card (Fin 2 → F) :=
      (Nat.card_congr (Equiv.ofInjective θ hinj)).symm
    rw [← hrange, h1, Nat.card_fun, Nat.card_fin]
  refine ⟨s.card, ?_, fun hm => ?_⟩
  · have h1 : Nat.card (s.sup id : AddSubgroup V) = ∏ W ∈ s, Nat.card W := card_sup_of_supIndep s hs
    rw [hsup, AddSubgroup.card_top] at h1
    rw [h1, Finset.prod_congr rfl hcard, Finset.prod_const]
  · obtain ⟨W₁, hW₁⟩ := Finset.card_eq_one.mp hm
    have hW₁s : W₁ ∈ s := by rw [hW₁]; exact Finset.mem_singleton_self _
    obtain ⟨-, -, -, θ, hinj, hrange, hθ⟩ := hW W₁ hW₁s
    have htop : W₁ = ⊤ := by
      have := hsup
      rw [hW₁, Finset.sup_singleton, id] at this
      exact this
    refine ⟨θ, ⟨hinj, fun v => ?_⟩, hθ⟩
    have hv : v ∈ θ.range := by rw [hrange, htop]; exact AddSubgroup.mem_top v
    exact hv

end CFSG.RankThree.GF2n.Tim78
