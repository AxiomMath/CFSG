module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313FA
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.H13.Lem3313F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

section Orders

variable {X : Type} [Group X]

theorem card_of_isPSL {n p e : ℕ} (h : IsPSL n p e X) :
    Nat.card X = (p ^ e) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1)) /
      Nat.gcd n (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by obtain ⟨⟨-, -, hn, -⟩, -⟩ := h; omega) h

theorem card_psl2_mod {q : ℕ} (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (h : IsPSL 2 q 1 X) : Nat.card X % 8 = 4 ∧ 660 ≤ Nat.card X := by
  have hc := card_of_isPSL h
  have h11 : 11 ≤ q := by omega
  have hg : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left (by omega)
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = 16 * a + 9 := by
    have h16 : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
    have h9 : q ^ 2 % 16 = 9 := by
      rcases h16 with h | h | h | h <;> simp [Nat.pow_mod, h]
    exact ⟨q ^ 2 / 16, by omega⟩
  have hN : Nat.card X = 4 * (q * (2 * a + 1)) := by
    rw [hc]
    simp only [pow_one, Finset.Icc_self, Finset.prod_singleton, hg]
    rw [show q ^ 2 - 1 = 16 * a + 8 by omega, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one,
      show q * (16 * a + 8) = 2 * (4 * (q * (2 * a + 1))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  have hB : q * (2 * a + 1) % 2 = 1 :=
    Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨hq.odd_of_ne_two (by omega), odd_two_mul_add_one a⟩)
  have h121 : 11 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h11 2
  have h165 : 11 * 15 ≤ q * (2 * a + 1) := Nat.mul_le_mul h11 (by omega)
  omega

theorem not_fiveShape_of_psl2 {q : ℕ} (hq : q.Prime)
    (h24 : q % 24 = 11 ∨ q % 24 = 13) (h : IsPSL 2 q 1 X) : ¬ FiveShape X := by
  obtain ⟨h8, h660⟩ := card_psl2_mod hq h24 h
  rintro (⟨n, hn⟩ | ⟨n, hn⟩ | hA | hn)
  · have hc := card_of_isPSL hn
    simp only [Finset.Icc_self, Finset.prod_singleton, show 2 * (2 - 1) / 2 = 1 from rfl,
      pow_one] at hc
    rcases n with _ | _ | _ | n
    · norm_num at hc
      omega
    · norm_num at hc
      omega
    · norm_num at hc
      omega
    · have hodd : Nat.Coprime 2 (2 ^ (n + 3) - 1) := by
        refine Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ?_)
        have h1 : 1 ≤ 2 ^ (n + 3) := Nat.one_le_two_pow
        have h2 : 2 ^ (n + 3) % 2 = 0 := by simp [Nat.pow_mod]
        omega
      rw [Nat.Coprime.gcd_eq_one hodd, Nat.div_one, show 2 ^ (n + 3) = 8 * 2 ^ n by ring,
        mul_assoc] at hc
      omega
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hn
    subst hf
    have hc : Nat.card X =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    have h8' : 8 ∣ 2 ^ (2 * a + 1) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      exact ⟨2 ^ (2 * b), by ring⟩
    have h8'' : 8 ∣ Nat.card X := by
      rw [hc]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow h8' two_ne_zero) _) _
    omega
  · obtain ⟨e⟩ := hA
    have hc : Nat.card X = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega
  · have hc := card_of_isPSL hn
    norm_num [Finset.prod_Icc_succ_top] at hc
    omega

end Orders

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem fiveShape_of_D36cConcl (hI5 : Insp5a) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hD : D31 M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hL38 : A38Types ↥L) (hVT : orbSup T V = ⊤) (hc : D36cConcl Mp T L V t) : FiveShape ↥L := by
  obtain ⟨hV0, -, hq, hab⟩ := hc
  rcases hab with hUV | ⟨hpsl, -⟩
  · have hU : commSub (orbSup T V) L = commV L := by rw [hVT, ← commV_eq_commSub]
    have hUV' : commV L = V := hU ▸ hUV
    exact (hI5 W M Mp T L V t hD hD.irr htT htL hMp hV0 hUV'
      (by rwa [qhatOf_autSub_congr hUV] at hq) hL38).1
  · exact Or.inr (Or.inr (Or.inr (isPSL_of_autSub_top hVT hpsl)))

end Module

variable {G : Type} [Group G] [Finite G]

theorem fiveShape_autOn (h316 : Theorem316Statement) (hD37 : D37) (hD36c : D36c) (hI5 : Insp5a)
    (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat) {T L V₀ : Subgroup G}
    (c : T326.Ctx T L V₀) [IsMulCommutative ↥(conjClosure V₀ T)]
    (hL38 : A38Types ↥(autOn L (conjClosure V₀ T))) :
    FiveShape ↥(autOn L (conjClosure V₀ T)) := by
  set V := conjClosure V₀ T with hV
  obtain ⟨s, hs, hsn⟩ := c.exists_t
  set t := conjAct V ⟨s⁻¹, T325.T_le_NV T V₀ (T.inv_mem hs)⟩ with ht
  have htT : t ∈ autOn T V := CtxV.conjAct_mem_autOn hs
  have htn := CtxV.not_mem_normalizer c hA37 hs hsn
  have hMp := CtxV.autOn_L₀_eq c hA37 hA38 hs hsn
  have hstd := CtxV.d3Std c h316
  have htop := CtxV.orbSup_eq_top (T := T) (V₀ := V₀)
  by_cases hVeq : V₀.subgroupOf V = ⊤
  · rcases hD37 ↥V _ _ _ _ _ hstd (hVeq.trans htop.symm) t htT htn hMp with
      ⟨n, hn, -⟩ | ⟨hn, -⟩
    · exact Or.inl ⟨n, isPSL_of_autSub_top hVeq hn⟩
    · exact Or.inr (Or.inr (Or.inr (isPSL_of_autSub_top hVeq hn)))
  · have hlt : V₀.subgroupOf V < orbSup (autOn T V) (V₀.subgroupOf V) := by
      rw [htop]
      exact lt_top_iff_ne_top.mpr hVeq
    rcases hD36c ↥V _ _ _ _ _ hstd hlt t htT htn hMp with hc | hc
    · exact fiveShape_of_D36cConcl hI5 hstd.hyp htT htn hMp hL38 htop hc
    · have hMp' : autOn (conjClosure L T) V =
          conjAutSub t (autOn L V) ⊔ conjAutSub t⁻¹ (conjAutSub t (autOn L V)) := by
        rw [conjAutSub_inv_conjAutSub, sup_comm]
        exact hMp
      have h5 := fiveShape_of_D36cConcl hI5 (hstd.hyp.conj htT) ((autOn T V).inv_mem htT)
        (not_mem_normalizer_conjAutSub htn) hMp' (a38Types_conjAutSub t hL38) htop hc
      exact fiveShape_congr (Subgroup.equivMapOfInjective (autOn L V) (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).symm h5

theorem nonempty_mulEquiv_autOn {T L V₀ : Subgroup G} (c : T326.Ctx T L V₀)
    (hS : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autOn L (conjClosure V₀ T))) := by
  set V := conjClosure V₀ T with hV
  have hL := CtxV.L_le_NV c
  let ψ : ↥L →* ↥(autOn L V) := (A4.actionOn V L hL).codRestrict (autOn L V)
    (fun l => (A4.mem_autOn_iff hL).2 ⟨l, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hL).1 ha
    exact ⟨l, rfl⟩
  have hker : CFSG.pCore 2 ↥L ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ((A4.actionOn_eq_one_iff hL x).2 (CtxV.pCoreOf_L_le c ⟨x, ?_, rfl⟩))
    exact hx
  let φ : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L V) := QuotientGroup.lift _ ψ hker
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨l, rfl⟩ := hψ a
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hnt : Nontrivial ↥(autOn L V) := CFSG.LocalCores.isQuasisimple_nontrivial (CtxV.quasi c)
  refine ⟨MulEquiv.ofBijective φ ⟨?_, hφ⟩⟩
  rcases hS.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff φ).mp h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(autOn L V))
    obtain ⟨g, rfl⟩ := hφ x
    exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

theorem false_of_ctx (h316 : Theorem316Statement) (hD37 : D37)
    (hD36c : D36c) (hI5 : Insp5a) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) {T L V₀ : Subgroup G} (c : T326.Ctx T L V₀) {q : ℕ}
    (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (hL : IsPSL 2 q 1 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have : IsMulCommutative ↥(conjClosure V₀ T) := c.elemV.1
  have hS : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 q 1 hL).2
  obtain ⟨e⟩ := nonempty_mulEquiv_autOn c hS
  have hL' : IsPSL 2 q 1 ↥(autOn L (conjClosure V₀ T)) := isPSL_congr e hL
  have h3 : 3 < q := by omega
  exact not_fiveShape_of_psl2 hq h24 hL'
    (fiveShape_autOn h316 hD37 hD36c hI5 hA37 hA38 c (Or.inr (Or.inr (Or.inr ⟨q, hq, h3, hL'⟩))))

end CFSG.Quasithin.H13.Lem3313F
