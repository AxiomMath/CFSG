module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem exists_equiv_map_eq {Γ X : Type} [Group Γ] [Finite Γ] [Group X] [Finite X]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (hX : Nonempty (X ≃* Γ)) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem unique_member_of_lattice {Γ X : Type} [Group Γ] [Finite Γ] [Group X] [Finite X]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (J : ℕ) (Y : ℕ → Subgroup Γ)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j) {j₀ : ℕ} (hj₀ : j₀ < J)
    (hdist : ∀ j ≤ J, j ≠ j₀ → Nat.card (memberOrTop J Y j) ≠ Nat.card (Y j₀))
    (hX : Nonempty (X ≃* Γ)) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    ∃ ψ : X ≃* Γ, T.map ψ.toMonoidHom = S ∧ ∀ Z : Subgroup X, T ≤ Z →
      Nat.card Z = Nat.card (Y j₀) → Z = (Y j₀).map ψ.symm.toMonoidHom := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_eq hS hX hT
  refine ⟨ψ, hψ, fun Z hTZ hcard => ?_⟩
  have hSZ : S ≤ Z.map ψ.toMonoidHom := by rw [← hψ]; exact Subgroup.map_mono hTZ
  obtain ⟨j, hj, hZ⟩ := hall _ hSZ
  have hc : Nat.card (memberOrTop J Y j) = Nat.card (Y j₀) := by
    rw [← hZ, Subgroup.card_map_of_injective ψ.injective, hcard]
  have hjj : j = j₀ := by
    by_contra hne
    exact hdist j hj hne hc
  subst hjj
  have hm : memberOrTop J Y j = Y j := by simp [memberOrTop, hj₀]
  rw [hm] at hZ
  have hid : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [← hZ, Subgroup.map_map, hid, Subgroup.map_id]

theorem noTwoQuot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ (N : Subgroup B) [N.Normal], IsPGroup 2 (B ⧸ N) → Nat.card (B ⧸ N) ≤ 1)
    (N : Subgroup A) [N.Normal] (hp : IsPGroup 2 (A ⧸ N)) : Nat.card (A ⧸ N) ≤ 1 := by
  let N' : Subgroup B := N.map e.toMonoidHom
  have hN' : N'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let q : (A ⧸ N) ≃* (B ⧸ N') := QuotientGroup.congr N N' e rfl
  have hp' : IsPGroup 2 (B ⧸ N') := hp.of_equiv q
  have := h N' hp'
  rwa [← Nat.card_congr q.toEquiv] at this

theorem noTwoQuot_map_equiv {Γ X : Type} [Group Γ] [Group X] (ψ : Γ ≃* X) (Y : Subgroup Γ)
    (h : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 1) :
    ∀ (N : Subgroup ↥(Y.map ψ.toMonoidHom)) [N.Normal],
      IsPGroup 2 (↥(Y.map ψ.toMonoidHom) ⧸ N) → Nat.card (↥(Y.map ψ.toMonoidHom) ⧸ N) ≤ 1 :=
  by
    intro N hN hp
    exact @noTwoQuot_of_equiv _ _ _ _ (ψ.subgroupMap Y).symm h N hN hp

theorem hrows_of_overgroups {X : Type} [Group X] [Finite X] {P K : Subgroup X}
    (hKtop : K ≠ ⊤) (hcardK : Nat.card K = 21 * Nat.card P)
    (huniq : ∀ Z : Subgroup X, P ≤ Z → Nat.card Z = Nat.card K → Z = K)
    (hov : ∀ Z : Subgroup X, P ≤ Z → Z ≠ ⊤ →
      (Nat.card Z = Nat.card P ∧ Nat.card (pCoreOf 2 Z) = Nat.card P) ∨
        Nat.card Z = 15 * Nat.card P ∨ Nat.card Z = 21 * Nat.card P ∨
        (Nat.card Z = 3 * Nat.card P ∧ Nat.card (pCoreOf 2 Z) * 2 = Nat.card P)) :
    ∀ N : Subgroup X, P ≤ N → N ≤ K → N ≠ K → Nat.card N = Nat.card P ∨
      (Nat.card N = 3 * Nat.card P ∧ Nat.card (pCoreOf 2 N) * 2 = Nat.card P) := by
  intro N hPN hNK hne
  have hNtop : N ≠ ⊤ := fun h => hKtop (top_le_iff.mp (h ▸ hNK))
  have hdvd : Nat.card N ∣ 21 * Nat.card P := hcardK ▸ Subgroup.card_dvd_of_le hNK
  have hPpos : 0 < Nat.card P := Nat.card_pos
  rcases hov N hPN hNtop with ⟨h1, -⟩ | h15 | h21 | h3
  · exact Or.inl h1
  · exfalso
    rw [h15] at hdvd
    exact absurd (Nat.dvd_of_mul_dvd_mul_right hPpos hdvd) (by norm_num)
  · exfalso
    exact hne (huniq N hPN (by rw [h21, hcardK]))
  · exact Or.inr h3

end CFSG.Quasithin.HSRuLoc.Mod
