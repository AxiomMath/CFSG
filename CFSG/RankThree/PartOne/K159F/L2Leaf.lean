module

public import CFSG.RankThree.PartOne.CTP.StrongPL2
public import CFSG.RankThree.PartOne.K159F.Witness

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.GorensteinWalter
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open Matrix

theorem card_ringEquiv_galoisField {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) :
    Nat.card (GaloisField p m ≃+* GaloisField p m) = m := by
  classical
  let K := GaloisField p m
  let : Fintype K := Fintype.ofFinite K
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  rw [Nat.card_congr e.toEquiv]
  have h1 := IsGalois.card_aut_eq_finrank (ZMod p) K
  have h2 : Module.finrank (ZMod p) (GaloisField p m) = m := GaloisField.finrank p hm
  exact h1.trans h2

theorem card_pGammaL2_two {p : ℕ} [Fact p.Prime] :
    Nat.card (PGammaL2 (GaloisField p 2)) = 2 * (p ^ 2 * (p ^ 4 - 1)) := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    card_ringEquiv_galoisField (by norm_num : (2 : ℕ) ≠ 0)]
  have h := CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField (p := p) (m := 2) (by norm_num)
  have h' : Nat.card (PGL2 (GaloisField p 2)) = p ^ 2 * (p ^ 4 - 1) := by
    have : p ^ (2 * 2) = p ^ 4 := by norm_num
    rw [this] at h
    exact h
  rw [h', mul_comm]

theorem false_of_l2_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (e : S ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 2))
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H}
    (hΩ : Nat.card (omegaOne p P) = p ^ 3) : False := by
  have hp : p.Prime := Fact.out
  have hKcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hdvdH : p ^ 3 ∣ Nat.card H := by
    rw [← hΩ]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : IsOddPrimePower (Nat.card (GaloisField p 2)) :=
    ⟨p, 2, hp, hp.odd_of_ne_two (by omega), by norm_num, hKcard⟩
  have h4 : 3 < Nat.card (GaloisField p 2) := by
    rw [hKcard]; nlinarith
  have hsurj := pGammaL2ToMulAutPSL2_surjective (GaloisField p 2) hKcard hodd h4
  let eAut := pGammaL2EquivMulAutPSL2 (GaloisField p 2) hodd h4 hsurj
  have hφ : Function.Injective (normalPSL2ConjAction S (GaloisField p 2) e) :=
    (MulAut.congr e).injective.comp (conjNormal_injective_of_centralizer S hSc)
  have hHdvd : Nat.card H ∣ Nat.card (MulAut (PSL2 (GaloisField p 2))) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hAut : Nat.card (MulAut (PSL2 (GaloisField p 2))) = 2 * (p ^ 2 * (p ^ 4 - 1)) := by
    rw [← Nat.card_congr eAut.toEquiv]
    exact card_pGammaL2_two
  have h5 : p ^ 3 ∣ 2 * (p ^ 2 * (p ^ 4 - 1)) := hAut ▸ hdvdH.trans hHdvd
  have h6 : p ∣ 2 * (p ^ 4 - 1) := by
    have h7 : p ^ 2 * p ∣ p ^ 2 * (2 * (p ^ 4 - 1)) := by
      have : p ^ 2 * (2 * (p ^ 4 - 1)) = 2 * (p ^ 2 * (p ^ 4 - 1)) := by ring
      rw [this]
      simpa [pow_succ] using h5
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h7
  rcases (Nat.Prime.dvd_mul hp).1 h6 with h8 | h8
  · have := Nat.le_of_dvd (by norm_num) h8
    omega
  · have h9 : p ∣ (p ^ 4 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
      exact dvd_pow_self p (by norm_num)
    exact hp.not_dvd_one ((Nat.dvd_add_right h8).mp h9)

theorem false_of_isoLie_A1_charP {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) = p ^ 3)
    (hord : ∀ a ∈ torusImage (omegaOne p P) S, orderOf a ≤ 6)
    {q : TauCeti.PrimePower} (hq : q.p = p) (h : IsoLie ↥S (.A 1 q)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hv, ⟨e⟩⟩ := h
  have hq' := hq
  subst hq
  have e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hexp := l2_charP hp5 q.exponent_pos.ne' S e' hSc hP (Or.inr hΩ)
  rcases hexp with h2 | h3
  · rw [h2] at e'
    exact false_of_l2_two hp5 S e' hSc hΩ
  · exact exists_large_automizer_of_isoLie_A1_three hp hp5 (inferInstance : S.Normal) q hq' h3
      ⟨hv, ⟨e⟩⟩ hP hΩ hord

end CFSG.RankThree.PartOne.K159F
