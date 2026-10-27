module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.StandardType.RCKU33

open CFSG.Assembly

@[expose] def GGInnCoprimeRank (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → ¬ p ∣ Nat.card R →
    ∀ E : Subgroup (MulAut R), CFSG.Open.IsElemAbelian p E → (∀ φ ∈ E, φ ∈ I) →
      Nat.card E ≤ p

@[expose] def GGInnCoprimeRankInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (GGInnCoprimeRank p)

theorem card_inf_centralizer_bound {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {B₁ D J L : Subgroup X}
    (hD : Nat.card ↥D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hJL : J ≤ L)
    {d : X} (hdD : d ∈ D) (hdL : d ∉ Subgroup.centralizer (L : Set X))
    (hB₁ : p ^ 4 ≤ Nat.card ↥B₁) :
    p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L : Set X)) ≤ Nat.card ↥B₁ := by
  set M := B₁ ⊓ Subgroup.centralizer (L : Set X)
  have hMD : M ≤ D := by
    rw [← hB₁J]
    exact fun g hg => ⟨hg.1, Subgroup.centralizer_le hJL hg.2⟩
  have hM : Nat.card ↥M ≤ p := by
    rcases card_eq_of_le_of_card_sq hp hMD hD with h | h | h
    · rw [h]; exact hp.one_lt.le
    · exact h.le
    · exact absurd ((Subgroup.eq_of_le_of_card_ge hMD (by rw [h, hD])).symm ▸ hdD).2 hdL
  calc p ^ 3 * Nat.card ↥M ≤ p ^ 3 * p := Nat.mul_le_mul_left _ hM
    _ = p ^ 4 := by ring
    _ ≤ Nat.card ↥B₁ := hB₁

theorem dvd_card_of_marking {X : Type} [Group X] [Finite X] (hIn : GGInnCoprimeRankInput) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ L : Subgroup X} (hB₁ : CFSG.Open.IsElemAbelian p B₁)
    (hB₁L : B₁ ≤ Subgroup.normalizer (L : Set X))
    (hmark : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hcard : p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L : Set X)) ≤ Nat.card ↥B₁) :
    p ∣ Nat.card ↥L := by
  by_contra hpL
  have hperf : Group.IsPerfect ↥L := ⟨hmark.1⟩
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun _ => True)
    (P' := GGInnCoprimeRank p) (fun lab hlab _ => hIn p hp hp2 lab hlab)
    (fun _ _ _ _ _ _ _ => trivial) hmark
  obtain ⟨R, _, I, F, hs, -, θ, hind, hco⟩ := largeEvenRawDatum_exists hraw
  let N := normalizerToCenterQuotientAut L B₁ hB₁L
  let T : MulAut (↥L ⧸ Subgroup.center ↥L) →* MulAut R :=
    { toFun := fun α => (θ.symm.trans α).trans θ
      map_one' := by ext r; simp
      map_mul' := fun α β => by ext r; simp }
  have hT : Function.Injective T := by
    intro α β h
    ext q
    have := congrArg (fun γ : MulAut R => θ.symm (γ (θ q))) h
    simpa [T] using this
  let ψ : ↥B₁ →* MulAut R := T.comp N
  have hEel : CFSG.Open.IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · rcases a with ⟨a, x, rfl⟩
      rcases b with ⟨b, y, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← map_mul]
      rw [hB₁.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      have hxp : x ^ p = 1 := Subtype.ext (by simpa using hB₁.2 (x : X) x.2)
      rw [← map_pow, hxp, map_one]
  have hEI : ∀ φ ∈ ψ.range, φ ∈ I := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hind (b : X)⁻¹ (B₁.inv_mem b.2)
    convert hφI using 1
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl' : (b : X) * l * (b : X)⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hB₁L b.2) l).mp l.2
      simpa using this
    rw [hφ l ⟨_, hl'⟩ (by simp)]
    show θ ((θ.symm.trans (N b)) (θ (QuotientGroup.mk l))) = _
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change θ (N b (QuotientGroup.mk' _ l)) = _
    rw [← normalizerConjAutOfMem_comp_mk]
    change θ (QuotientGroup.mk _) = θ (QuotientGroup.mk _)
    congr 2
  have hE3 : p ^ 3 ≤ Nat.card ψ.range := by
    have hkerle : Nat.card ψ.ker ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L : Set X)) := by
      have hsub : ψ.ker.map B₁.subtype ≤ B₁ ⊓ Subgroup.centralizer (L : Set X) := by
        rintro _ ⟨b, hb, rfl⟩
        have h1 : N b = 1 := hT (by rw [map_one]; exact hb)
        exact (normalizerToCenterQuotientAut_eq_one_iff hperf hB₁L b).1 h1
      rw [← Subgroup.card_map_of_injective (f := B₁.subtype) Subtype.val_injective]
      exact Subgroup.card_le_of_le hsub
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have hquot : Nat.card (↥B₁ ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have hpos : 0 < Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L : Set X)) := Nat.card_pos
    rw [hlag, hquot] at hcard
    have h2 := le_trans hcard (Nat.mul_le_mul_left _ hkerle)
    exact Nat.le_of_mul_le_mul_right h2 hpos
  have hpR : ¬ p ∣ Nat.card R := by
    intro h
    apply hpL
    have h1 : Nat.card R = Nat.card (↥L ⧸ Subgroup.center ↥L) := Nat.card_congr θ.symm.toEquiv
    rw [h1] at h
    exact h.trans (Subgroup.card_quotient_dvd_card _)
  have hle := hco hs hpR ψ.range hEel hEI
  have : p ^ 3 ≤ p := hE3.trans hle
  have h1 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

section Main

theorem u33_card_ne_6048_of_input
    {X : Type} [Group X] [Finite X] (hIn : GGInnCoprimeRankInput) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {G₀ A B₁ D J L : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hB₁A : B₁ ≤ A) (hDB₁ : D ≤ B₁)
    (hD : Nat.card ↥D = p ^ 2) (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hB₁ : p ^ 4 ≤ Nat.card ↥B₁) (hB₁L : B₁ ≤ Subgroup.normalizer (L : Set X))
    (hmark : CFSG.StandardType.LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      CFSG.Assembly.LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ))
    (hLx : ∃ x ∈ D, x ≠ 1 ∧
      CFSG.Assembly.IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set X)))
    (hDL : ¬ D ≤ Subgroup.centralizer (L : Set X))
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 6048 := by
  obtain ⟨d, hdD, hdL⟩ := Set.not_subset.1 hDL
  have hJL : J ≤ L := (CFSG.Assembly.isComponentOf_iff_open.1 hJ).1.trans inf_le_left
  have hAel : CFSG.Open.IsElemAbelian p B₁ :=
    ⟨⟨⟨fun a b => by
      have := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hB₁A a.2⟩ ⟨b, hB₁A b.2⟩)
      exact Subtype.ext this⟩⟩, fun y hy => hA.2 y (hB₁A hy)⟩
  have hpL := dvd_card_of_marking hIn hp hp2 hAel hB₁L hmark
    (card_inf_centralizer_bound hp hD hB₁J hJL hdD hdL hB₁)
  exact u33_card_ne_6048 hp hp2 hA hB₁A hDB₁ hD hB₁J hB₁ hB₁L hmark hLx hDL hJ hpL

end Main

end CFSG.StandardType.RCKU33
