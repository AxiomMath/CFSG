module

public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.AppendixH.H15.H157Class
public import CFSG.Quasithin.AppendixH.H15.H157Avoid

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code

theorem Is3A.card_fixW {y : ↥AutPerm} (hy : Is3A y) : Nat.card ↥(fixW y) = 32 := by
  obtain ⟨c, hc⟩ := hy
  calc Nat.card ↥(fixW y) = Nat.card ↥(fixW (c * y * c⁻¹)) := (card_fixW_conj c y).symm
    _ = Nat.card ↥(fixW tA) := by rw [hc]
    _ = 32 := card_fixW_tA

theorem Is3A.rk_fixW {y : ↥AutPerm} (hy : Is3A y) : rk ↥(fixW y) = 5 := by
  unfold rk
  rw [hy.card_fixW]
  show padicValNat 2 (2 ^ 5) = 5
  exact padicValNat.prime_pow (p := 2) 5

theorem isVecOf_iff {a b : Fin 24} {V : Type} [CommGroup V]
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (e : V ≃* W11)
    (hβe : ∀ (v : V) (m : ↥(G6.coreMod 24)), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
      e v = cocodeCoords.κ m)
    {u : PM24} (hu : u ∈ G6.coreMod 24) (x : V) :
    IsVecOf (mathModel false 24 a b M24g) β u x ↔ e x = cocodeCoords.κ u := by
  constructor
  · rintro ⟨he, hβ⟩
    exact (hβe x ⟨u, he⟩).1 hβ
  · intro h
    exact ⟨hu, (hβe x ⟨u, hu⟩).2 h⟩

theorem isVecOf_pair_of_eq {a b : Fin 24} {V : Type} [CommGroup V]
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (e : V ≃* W11)
    (hβe : ∀ (v : V) (m : ↥(G6.coreMod 24)), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
      e v = cocodeCoords.κ m)
    (i j : Fin 24) (v : V) (h : e v = cocodeCoords.κ (pairVec i j)) :
    IsVecOf (mathModel false 24 a b M24g) β (pairVec i j) v := by
  exact (isVecOf_iff β e hβe (pairVec_mem_coreMod i j) v).2 h


theorem sixteen_le_card_fixW {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24} (hy : y ∈ M24g)
    (h4 : 4 ≤ rk ↥(fixV (rImg ρ (Subgroup.zpowers y)))) : 16 ≤ Nat.card ↥(fixW ⟨y, hy⟩) := by
  have h4' : 4 ≤ rk ↥(fixW ⟨y, hy⟩) := by
    rw [← rk_fixV_zpowers ρ e he hy]
    exact h4
  unfold rk at h4'
  have hdvd : 2 ^ 4 ∣ Nat.card ↥(fixW ⟨y, hy⟩) :=
    (pow_dvd_pow 2 h4').trans pow_padicValNat_dvd
  have := Nat.le_of_dvd Nat.card_pos hdvd
  norm_num at this
  exact this

theorem fixV_iff_core {a b : Fin 24} {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (e : V ≃* W11) (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v))
    (hβe : ∀ (v : V) (m : ↥(G6.coreMod 24)), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
      e v = cocodeCoords.κ m)
    {y : S24} (hy : y ∈ M24g) (h3A : Is3A ⟨y, hy⟩) (x : V) :
    x ∈ fixV (rImg ρ (Subgroup.zpowers y)) ↔
      ∃ u : PM24, u ∈ G6.coreMod 24 ∧ (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) ∧
        IsVecOf (mathModel false 24 a b M24g) β u x := by
  rw [mem_fixV_zpowers_iff_fixW ρ e he hy x]
  constructor
  · intro hx
    obtain ⟨u, hu, hsupp, hκ⟩ := (mem_fixW_iff_core h3A (e x)).1 hx
    exact ⟨u, hu, fun i hi => hsupp i hi,
      (isVecOf_iff β e hβe hu x).2 hκ.symm⟩
  · rintro ⟨u, hu, hsupp, hv⟩
    exact (mem_fixW_iff_core h3A (e x)).2
      ⟨u, hu, fun i hi => hsupp i hi, ((isVecOf_iff β e hβe hu x).1 hv).symm⟩

theorem h157_main
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (cfg : Cfg14 a b O Tr S B T₀) {V : Type} [CommGroup V]
    (ρ : ↥M24g →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (hreal : RealizesBy (mathModel false 24 a b M24g) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    (Mx : Subgroup S24) (hMx : Mx = M24g ∨ Mx = M23g a) (y : S24) (hy : y ∈ Mx)
    (hp : (orderOf y).Prime) (hodd : Odd (orderOf y))
    (h4 : 4 ≤ rk ↥(fixV (rImg ρ (Subgroup.zpowers y)))) :
    (orderOf y = 3 ∧ rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) = 5 ∧
      ∃ g ∈ M24g,
        (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊓
            KY M24g S = ⊥ ∧
        (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊔
            KY M24g S = MY M24g S ∧
        fixV (rImg ρ (KY M24g S)) =
          fixV (rImg ρ (M24g ⊓ Subgroup.normalizer
            ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) ∧
        ∃ π : ↥(M24g ⊓ Subgroup.normalizer
            ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) →* Equiv.Perm (Fin 6),
          Function.Surjective π ∧
          π.ker = (conjSubg g (Subgroup.zpowers y)).subgroupOf
            (M24g ⊓ Subgroup.normalizer
              ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ∧
          ∃ coordinates : Fin 6 ↪ Fin 24,
            (∀ point : Fin 24, (g * y * g⁻¹) point = point ↔
              ∃ index : Fin 6, coordinates index = point) ∧
            ∀ (acting : ↥(M24g ⊓ Subgroup.normalizer
                ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) (index : Fin 6),
              (acting : S24) (coordinates index) = coordinates (π acting index)) ∧
    (∀ x : V, x ∈ fixV (rImg ρ (Subgroup.zpowers y)) ↔
      ∃ u : PM24, u ∈ G6.coreMod 24 ∧ (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) ∧
        IsVecOf (mathModel false 24 a b M24g) β u x) ∧
    (∀ u : PM24, u ≠ 1 → u ∈ G6.coreMod 24 →
      (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) → u ∉ golayC) ∧
    (∀ I : Subgroup V, I ≤ fixV (rImg ρ (Subgroup.zpowers y)) →
      (Mx = M24g → (∀ x ∈ I, ¬ IsO2Vec 24 a b M24g β x) → rk ↥I ≤ 2) ∧
      (Mx = M23g a → (∀ x ∈ I, ¬ ∃ j : Fin 24, j ≠ a ∧
        IsVecOf (mathModel false 24 a b M24g) β (pairVec a j) x) → rk ↥I ≤ 4)) := by
  have hreal' : RealizesBy (FFModel.golaySec M24g (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
      ρ.rangeRestrict β := hreal
  obtain ⟨e, he, -, hβe⟩ := exists_equiv_cocodeStd (Γ := M24g) le_rfl hreal'
  have hyA : y ∈ M24g := by
    rcases hMx with h | h
    · exact h ▸ hy
    · exact ((mem_M23g_iff a y).1 (h ▸ hy)).1
  have hya : Mx = M23g a → y a = a :=
    fun h => ((mem_M23g_iff a y).1 (h ▸ hy)).2
  let y' : ↥AutPerm := ⟨y, hyA⟩
  have hord : orderOf y' = orderOf y := Subgroup.orderOf_mk y hyA
  have h16 : 16 ≤ Nat.card ↥(fixW y') := sixteen_le_card_fixW ρ e he hyA h4
  have h3A : Is3A y' := classify_odd y' (hord.symm ▸ hp) (hord.symm ▸ hodd) h16
  have hord3 : orderOf y = 3 := by
    rw [← hord]
    exact Is3A.orderOf_eq h3A
  have hrk : rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) = 5 := by
    rw [rk_fixV_zpowers ρ e he hyA, Is3A.rk_fixW h3A]
  have h3A' : Is3A y' := h3A
  obtain ⟨c, hc⟩ := h3A'
  have hcy : (c : S24) * y * (c : S24)⁻¹ = tP := by
    have := congrArg Subtype.val hc
    simpa [tA] using this
  obtain ⟨h, hh, hSh⟩ := sextet_normal_form cfg.sextet
  subst hSh
  refine ⟨⟨hord3, hrk, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨h * (c : S24), M24g.mul_mem hh c.2, ?_, ?_, ?_, ?_⟩
    · exact frame_inf (y := y) (c := (c : S24)) hh hcy
    · exact frame_sup (y := y) (c := (c : S24)) hh hcy
    · exact fixV_KY_eq_fixV_N ρ e he hh hcy
    · exact frame_pi (y := y) (c := (c : S24)) hh hcy
  · exact fun x => fixV_iff_core ρ β e he hβe hyA h3A x
  · intro u hu1 hu hsupp
    exact not_mem_golayC_of_fix h3A hu1 hsupp
  · intro I hI
    refine ⟨?_, ?_⟩
    · intro hM hIO
      exact rk_le_two_of_avoid ρ e he hyA h3A (fun v => IsO2Vec 24 a b M24g β v)
        (fun v i j hij hv => ⟨i, j, hij, Or.inl rfl, isVecOf_pair_of_eq β e hβe i j v hv⟩)
        I hI hIO
    · intro hM hIO
      exact rk_le_four_of_avoid ρ e he hyA h3A (hya hM)
        (fun v => ∃ j : Fin 24, j ≠ a ∧
          IsVecOf (mathModel false 24 a b M24g) β (pairVec a j) v)
        (fun v j hj hv => ⟨j, hj, isVecOf_pair_of_eq β e hβe a j v hv⟩) I hI hIO

end CFSG.ASVolI.AppH.H157
