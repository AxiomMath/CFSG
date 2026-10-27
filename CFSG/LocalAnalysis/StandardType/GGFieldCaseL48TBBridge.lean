module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace TableBBridge

theorem mem_normalizer_of_conj_mem
    {M : Type} [Group M] [Finite M] {H : Subgroup M} {g : M} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set M) := by
  have := mem_normalizer_of_forall_conj_mem (W := H) (g := g⁻¹) (fun x hx => by simpa using h x hx)
  simpa using Subgroup.inv_mem _ this

theorem card_inf_centralizer_le
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) :
    Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ≤ p := by
  obtain ⟨-, hEA, -, -, h5, -⟩ := hP
  have hDE : E ⊓ Subgroup.centralizer (L' : Set M) ≤ E := inf_le_left
  have hcyc : IsCyclic (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    h5 _ (hDE.trans le_sup_left) inf_le_right (isPGroup_of_isElemAbelian (isElemAbelian_mono hEA hDE))
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg1 : g ^ p = 1 := Subtype.ext (by simpa using hEA.2 g (hDE g.2))
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hg1)

theorem card_eq_card_range_mul
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} (hE' : E ≤ Subgroup.normalizer (L' : Set M)) :
    Nat.card E = Nat.card (ggGamma L' hE').range *
      Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  have h1 := TableB.card_range_mul_card_ker (ggGamma L' hE')
  have hker : (ggGamma L' hE').ker =
      (E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker] at h1
  have h2 : Nat.card ((E ⊓ Subgroup.centralizer (L' : Set M)).subgroupOf E) =
      Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem pow_le_card_range_of_torusLift
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} {r : ℕ} (hP : GGTableBPosition p L' E I θ hE)
    (hp : p.Prime) (hL : GGTorusLift p r R) : p ^ r ≤ Nat.card (ggGamma L' hE).range := by
  obtain ⟨hperf, hEA, -, -, -, -, h7⟩ := hP
  obtain ⟨U, E₀, hU, hU2, hE₀U, hE₀A, hE₀card, hE₀ker⟩ := hL L' (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  rw [ker_ggQuotHom] at hE₀ker
  have hDE : E ⊓ Subgroup.centralizer (L' : Set M) ≤ E := inf_le_left
  have hE₀'L : E₀.map L'.subtype ≤ L' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hU'L : U.map L'.subtype ≤ L' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hDcomm : ∀ x ∈ E₀.map L'.subtype, ∀ d ∈ E ⊓ Subgroup.centralizer (L' : Set M),
      x * d = d * x := fun x hx d hd => Subgroup.mem_centralizer_iff.mp hd.2 x (hE₀'L hx)
  have hbot : ∀ y : M, y ∈ E₀.map L'.subtype → y ∈ E ⊓ Subgroup.centralizer (L' : Set M) →
      y = 1 := by
    rintro _ ⟨l, hl, rfl⟩ hy
    have hlc : l ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 g g.2)
    have : l ∈ E₀ ⊓ Subgroup.center L' := ⟨hl, hlc⟩
    rw [hE₀ker, Subgroup.mem_bot] at this
    simp [this]
  have hElem : IsElemAbelian p (E₀.map L'.subtype ⊔ E ⊓ Subgroup.centralizer (L' : Set M)) :=
    isElemAbelian_sup (isElemAbelian_map hE₀A L'.subtype) (isElemAbelian_mono hEA hDE) hDcomm
  have hnorm : E₀.map L'.subtype ⊔ E ⊓ Subgroup.centralizer (L' : Set M) ≤
      Subgroup.normalizer ((U.map L'.subtype : Subgroup M) : Set M) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      refine mem_normalizer_of_conj_mem fun g hg => ?_
      obtain ⟨u, hu, rfl⟩ := hg
      have h1 := (Subgroup.mem_normalizer_iff.mp (hE₀U hx) u).mp hu
      exact ⟨_, h1, by simp⟩
    · intro d hd
      refine mem_normalizer_of_conj_mem fun g hg => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hd.2 g (hU'L hg)
      rw [← h1, mul_inv_cancel_right]
      exact hg
  have hU'ne : U.map L'.subtype ≠ ⊥ := fun h =>
    hU (Subgroup.map_injective L'.subtype_injective (h.trans (Subgroup.map_bot _).symm))
  have h7' := h7 _ _ (sup_le (hE₀'L.trans le_sup_right) (hDE.trans le_sup_left))
    (hU'L.trans le_sup_right) hElem hU'ne (hU2.map L'.subtype) hnorm
  let f : (E₀.map L'.subtype) × (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) →
      ↥(E₀.map L'.subtype ⊔ E ⊓ Subgroup.centralizer (L' : Set M)) := fun xd =>
    ⟨xd.1 * xd.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left xd.1.2)
      (Subgroup.mem_sup_right xd.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨d, hd⟩⟩ ⟨⟨x', hx'⟩, ⟨d', hd'⟩⟩ h
    have h' : x * d = x' * d' := congrArg Subtype.val h
    have hy : x'⁻¹ * x = d' * d⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * d) * d⁻¹ := by group
        _ = x'⁻¹ * (x' * d') * d⁻¹ := by rw [h']
        _ = d' * d⁻¹ := by group
    have h1 : x'⁻¹ * x = 1 :=
      hbot _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx') hx)
        (hy ▸ Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd))
    have hxx : x = x' := (inv_mul_eq_one.mp h1).symm
    subst hxx
    have h2 : d' * d⁻¹ = 1 := hy ▸ h1
    have hdd : d = d' := (mul_inv_eq_one.mp h2).symm
    subst hdd
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hc
  have hE₀c : Nat.card (E₀.map L'.subtype) = p ^ r := by
    rw [← hE₀card]
    exact (Nat.card_congr (E₀.equivMapOfInjective L'.subtype L'.subtype_injective).toEquiv).symm
  rw [hE₀c] at hc
  have hcE := card_eq_card_range_mul (L' := L') (E := E) hE
  have hpos : 0 < Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) :=
    Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← hcE]
  exact hc.trans h7'

theorem mem_normalizer_of_witness
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) (n : L')
    (hn : ∀ a ∈ (ggGamma L' hE).range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ (ggGamma L' hE).range, a' (n * (a n)⁻¹) = n * (a n)⁻¹) :
    (n : M) ∈ Subgroup.normalizer (E : Set M) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hP
  refine mem_normalizer_of_conj_mem fun e he => ?_
  obtain ⟨htp, htA⟩ := hn (ggGamma L' hE ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩
  have htG : ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) = n * e * (n : M)⁻¹ * e⁻¹ := by
    push_cast
    rw [ggGamma_coe]
    group
  have htC : ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) ∈
      Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have h1 := congrArg Subtype.val (htA (ggGamma L' hE ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
    rw [ggGamma_coe] at h1
    calc b' * ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M)
        = b' * ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) * b'⁻¹ * b' := by group
      _ = ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) * b' := by rw [h1]
  have htp' : ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) ^ p = 1 := by
    have := congrArg Subtype.val htp
    simpa using this
  have htE := h6 _ (Subgroup.mem_sup_right (n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹).2) htC htp'
  have e' : (n : M) * e * (n : M)⁻¹ =
      ((n * (ggGamma L' hE ⟨e, he⟩ n)⁻¹ : L') : M) * e := by
    rw [htG]
    group
  rw [e']
  exact E.mul_mem htE he

theorem ggTorusSelfCent_range
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) :
    GGTorusSelfCent p (ggGamma L' hE).range := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hP
  intro n hn hnp
  have hnC : (n : M) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : b * (n : M) * b⁻¹ = n := by
      have := congrArg Subtype.val (hn (ggGamma L' hE ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at this
      exact this
    calc b * (n : M) = b * n * b⁻¹ * b := by group
      _ = n * b := by rw [h1]
  have hnp' : (n : M) ^ p = 1 := by
    have := congrArg Subtype.val hnp
    simpa using this
  refine ⟨⟨n, h6 _ (Subgroup.mem_sup_right n.2) hnC hnp'⟩, ?_⟩
  ext l
  simp [ggGamma_coe, MulAut.conj_apply]

theorem isElemAbelian_range_gamma
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) :
    IsElemAbelian p (ggGamma L' hE).range := by
  obtain ⟨-, hEA, -⟩ := hP
  exact isElemAbelian_range (fun a b => Subtype.ext (IsElemAbelian.comm hEA a.2 b.2))
    (fun b => Subtype.ext (by simpa using hEA.2 b b.2)) _

theorem induces_range_gamma
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) :
    ∀ a ∈ (ggGamma L' hE).range, ∃ φ ∈ I, ∀ l : L', φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
  obtain ⟨-, -, -, h4, -⟩ := hP
  rintro _ ⟨b, rfl⟩
  exact ⟨ggBeta L' θ hE b, h4 b, fun l => ggBeta_ggQuotHom L' hE θ b l⟩

theorem pow_three_le_card_range
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) :
    p ^ 3 ≤ Nat.card (ggGamma L' hE).range := by
  have h4 : p ^ 4 ≤ Nat.card E := hP.2.2.1
  have hD := card_inf_centralizer_le hP hp
  rw [card_eq_card_range_mul (L' := L') (E := E) hE] at h4
  have : p ^ 3 * p ≤ Nat.card (ggGamma L' hE).range * p :=
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ _ := h4
      _ ≤ _ := Nat.mul_le_mul_left _ hD
  exact Nat.le_of_mul_le_mul_right this hp.pos

theorem pow_pred_le_card_range
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) (hp : p.Prime) {r : ℕ}
    (hr : p ^ r ≤ Nat.card E) : p ^ (r - 1) ≤ Nat.card (ggGamma L' hE).range := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [Nat.zero_sub, pow_zero]
    exact Nat.card_pos
  · have hD := card_inf_centralizer_le hP hp
    rw [card_eq_card_range_mul (L' := L') (E := E) hE] at hr
    have : p ^ (r - 1) * p ≤ Nat.card (ggGamma L' hE).range * p :=
      calc p ^ (r - 1) * p = p ^ r := by rw [← pow_succ]; congr 1; omega
        _ ≤ _ := hr
        _ ≤ _ := Nat.mul_le_mul_left _ hD
    exact Nat.le_of_mul_le_mul_right this hp.pos

theorem irred_of_witness
    {M : Type} [Group M] [Finite M] {L' : Subgroup M} {E : Subgroup M} {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {p : ℕ} (hP : GGTableBPosition p L' E I θ hE) {W : Set L'}
    (hW1 : ∀ n ∈ W, ∀ a ∈ (ggGamma L' hE).range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ (ggGamma L' hE).range, a' (n * (a n)⁻¹) = n * (a n)⁻¹)
    (hW2 : ∀ A' : Subgroup (MulAut L'), A' ≤ (ggGamma L' hE).range →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') →
      A' = ⊥ ∨ A' = (ggGamma L' hE).range) :
    ∀ S : Subgroup M, E ⊓ Subgroup.centralizer (L' : Set M) ≤ S → S ≤ E →
      (∀ n ∈ L' ⊓ Subgroup.normalizer (E : Set M), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = E ⊓ Subgroup.centralizer (L' : Set M) ∨ S = E := by
  intro S hDS hSE hSinv
  set γ := ggGamma L' hE with hγ
  have hWN : ∀ n ∈ W, (n : M) ∈ L' ⊓ Subgroup.normalizer (E : Set M) := fun n hn =>
    ⟨n.2, mem_normalizer_of_witness hP n (hW1 n hn)⟩
  have hker : ∀ b : E, γ b = 1 ↔ (b : M) ∈ E ⊓ Subgroup.centralizer (L' : Set M) := fun b => by
    rw [hγ, ggGamma_eq_one_iff]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hconj : ∀ n ∈ W, ∀ b : E, ∃ hnb : (n : M) * b * (n : M)⁻¹ ∈ E,
      γ ⟨(n : M) * b * (n : M)⁻¹, hnb⟩ = MulAut.conj n * γ b * (MulAut.conj n)⁻¹ := by
    intro n hn b
    have hnb : (n : M) * b * (n : M)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hWN n hn).2 b).mp b.2
    exact ⟨hnb, ggGamma_conj L' hE n b hnb⟩
  set A' : Subgroup (MulAut L') := (S.subgroupOf E).map γ with hA'
  have hA'A : A' ≤ γ.range := by
    rintro _ ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
    rintro n hn _ ⟨s, hs, rfl⟩
    obtain ⟨hns, he⟩ := hconj n hn s
    exact ⟨⟨_, hns⟩, Subgroup.mem_subgroupOf.mpr
      (hSinv n (hWN n hn) s (Subgroup.mem_subgroupOf.mp hs)), he⟩
  rcases hW2 A' hA'A hA'inv with h | h
  · left
    refine le_antisymm (fun s hs => ?_) hDS
    have h1 : γ ⟨s, hSE hs⟩ ∈ A' := ⟨⟨s, hSE hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (hker _).mp h1
  · right
    refine le_antisymm hSE (fun b hb => ?_)
    have h1 : γ ⟨b, hb⟩ ∈ A' := h ▸ ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨s, hs, hsb⟩ := h1
    have h2 : γ (⟨b, hb⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hsb, mul_inv_cancel]
    have h3 : (b : M) * (s : M)⁻¹ ∈ S := hDS ((hker _).mp h2)
    have e : b = (b * (s : M)⁻¹) * s := by group
    rw [e]
    exact S.mul_mem h3 (Subgroup.mem_subgroupOf.mp hs)

end TableBBridge

open TableBBridge

theorem ggIrredModTableB_of_torusIrred {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hL : GGTorusLift p r R) (hI : GGTorusIrred p r R I) :
    GGIrredModTableB p R I := by
  intro M _ _ L' E θ hE hP S hDS hSE hSinv
  obtain ⟨W, hW1, hW2, -, -⟩ := hI L' (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hP.1 (ggGamma L' hE).range (isElemAbelian_range_gamma hP)
    (induces_range_gamma hP) (pow_le_card_range_of_torusLift hP hp hL)
    (pow_three_le_card_range hP hp)
  exact irred_of_witness hP hW1 hW2 S hDS hSE hSinv

theorem ggIrredModTableB_of_torusIrredSCr {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hL : GGTorusLift p r R) (hI : TwE6TB.GGTorusIrredSCr p r R I) :
    GGIrredModTableB p R I := by
  intro M _ _ L' E θ hE hP S hDS hSE hSinv
  obtain ⟨W, hW1, hW2, -, -⟩ := hI L' (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hP.1 (ggGamma L' hE).range (isElemAbelian_range_gamma hP)
    (induces_range_gamma hP) (pow_le_card_range_of_torusLift hP hp hL)
    (pow_three_le_card_range hP hp) (ggTorusSelfCent_range hP)
  exact irred_of_witness hP hW1 hW2 S hDS hSE hSinv

theorem largeEvenLabelAll_irredModTableB_of_torusIrredSCr {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ TwE6TB.GGTorusIrredSCr p r R I) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I :=
  h.mono fun _ _ _ _ ⟨_, hl, hi⟩ => Or.inl (ggIrredModTableB_of_torusIrredSCr hp hl hi)

theorem ggIrredModTableB_of_torusIrredSC {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hI : CorFourTwoOpen.GGTorusIrredSC p R I) : GGIrredModTableB p R I := by
  intro M _ _ L' E θ hE hP S hDS hSE hSinv
  obtain ⟨W, hW1, hW2, -, -⟩ := hI L' (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hP.1 (ggGamma L' hE).range (isElemAbelian_range_gamma hP)
    (induces_range_gamma hP) (pow_three_le_card_range hP hp) (ggTorusSelfCent_range hP)
  exact irred_of_witness hP hW1 hW2 S hDS hSE hSinv

theorem ggIrredModTableBRk_of_torusIrred {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hI : GGTorusIrred p (r - 1) R I) : GGIrredModTableBRk p R I r := by
  intro M _ _ L' E θ hE hP hr S hDS hSE hSinv
  obtain ⟨W, hW1, hW2, -, -⟩ := hI L' (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hP.1 (ggGamma L' hE).range (isElemAbelian_range_gamma hP)
    (induces_range_gamma hP) (pow_pred_le_card_range hP hp hr) (pow_three_le_card_range hP hp)
  exact irred_of_witness hP hW1 hW2 S hDS hSE hSinv

theorem largeEvenLabelAll_irredModTableB_of_torusIrred {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I :=
  h.mono fun _ _ _ _ ⟨_, hl, hi⟩ => Or.inl (ggIrredModTableB_of_torusIrred hp hl hi)

end CFSG.StandardType

end
