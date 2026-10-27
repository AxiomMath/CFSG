module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBHomocyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTableBPosition (p : ℕ) {M : Type} [Group M] (L' E : Subgroup M) {R : Type}
    [Group R] (I : Set (MulAut R)) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)) : Prop :=
  commutator L' = ⊤ ∧ IsElemAbelian p E ∧ p ^ 4 ≤ Nat.card E ∧
    (∀ e : E, ggLAut L' θ ⟨e, hE e.2⟩ ∈ I) ∧
    (∀ S : Subgroup M, S ≤ E ⊔ L' → S ≤ Subgroup.centralizer (L' : Set M) → IsPGroup p S →
      IsCyclic S) ∧
    (∀ g ∈ E ⊔ L', g ∈ Subgroup.centralizer (E : Set M) → g ^ p = 1 → g ∈ E) ∧
    ∀ E' T : Subgroup M, E' ≤ E ⊔ L' → T ≤ E ⊔ L' → IsElemAbelian p E' → T ≠ ⊥ →
      IsPGroup 2 T → E' ≤ Subgroup.normalizer (T : Set M) → Nat.card E' ≤ Nat.card E

@[expose] def GGCoverPTableB (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ ρ : R, ∀ e : E, Commute ((MulAut.conj ρ)⁻¹ * a) (ggLAut L' θ ⟨e, hE e.2⟩)

@[expose] def GGIrredTableB (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    Nat.card E = p ^ 4 * Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ∧
    ∀ S : Subgroup M, E ⊓ Subgroup.centralizer (L' : Set M) ≤ S → S ≤ E →
      (∀ n ∈ L' ⊓ Subgroup.normalizer (E : Set M), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = E ⊓ Subgroup.centralizer (L' : Set M) ∨ S = E

@[expose] def GGD4Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ lab.rank = 4 ∧ p = 3

theorem tableBPosition_of_config {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R) (hL : commutator L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    GGTableBPosition p L Bs I θ hBsN := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hβ := hcfg.1.2.2.2.2.2.1
  have hsS := hcfg.1.2.2.2.2.2.2.1
  have hBst := hcfg.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBst.1
  refine ⟨hL, hBst.2.1, (pow_four_le_card_of_bmax hp hsS.1 hβ.2.2.2).trans hBBs,
    fun e => ggLAut_mem_of_induces L θ hBsN h3 e.2, fun S _ hSC hSp => hsS.2.2.2.2 S hSC hSp,
    fun g _ hgC hgp => hBst.2.2.2 g hgC hgp, ?_⟩
  intro E' T _ _ hE' hT hT2 hE'T
  have hc := card_le_of_twoLocal hp ⟨T, hT, hT2, rfl⟩ hE'T hE'
  rw [← hsS.1.2.1] at hc
  exact hc.trans hBBs

theorem tableBPosition_of_setup {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R) (hL : commutator L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    GGTableBPosition p L Bs I θ hBsN :=
  tableBPosition_of_config hS.1.1 θ hL hBsN h3

theorem coverP_at_of_tableB {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hKG : GGCoverPTableB p R I) :
    ∀ h ∈ Subgroup.centralizer ({x} : Set G), (∃ k : ℕ, h ^ p ^ k = 1) →
      h ∈ (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) ⊔
        L ⊔ (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (L : Set G)) := by
  intro h hh ⟨k, hk⟩
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  set hN' : Subgroup.normalizer (L : Set G) := ⟨h, hN hh⟩ with hhN
  have ha : ggLAut L θ hN' ^ p ^ k = 1 := by
    rw [← map_pow]
    have : hN' ^ p ^ k = 1 := Subtype.ext (by simpa [hhN] using hk)
    rw [this, map_one]
  obtain ⟨ρ, hρ⟩ := hKG G L Bs θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3) _ ⟨k, ha⟩
  obtain ⟨q, rfl⟩ := θ.surjective ρ
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  have hℓH : (ℓ : G) ∈ Subgroup.centralizer ({x} : Set G) := hLx ℓ.2
  set g := (ℓ : G)⁻¹ * h with hg
  have hgH : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hℓH) hh
  set gN : Subgroup.normalizer (L : Set G) := ⟨g, hN hgH⟩ with hgN
  have hgA : ggLAut L θ gN =
      (MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN' := by
    rw [← ggLAut_of_mem_conj θ ℓ (hN hℓH), ← map_inv, ← map_mul]
    congr 1
  have hcomm : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G),
      g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro b hb
    set bN : Subgroup.normalizer (L : Set G) := ⟨b, hBsN hb.1⟩ with hbN
    have h1 : ggLAut L θ (gN * bN * gN⁻¹ * bN⁻¹) = 1 := by
      have hc := (hρ ⟨b, hb.1⟩).eq
      simp only [map_mul, map_inv]
      rw [hgA]
      change _ * ggLAut L θ bN * _ * _ = 1 at *
      have hc' : ((MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN') * ggLAut L θ bN =
          ggLAut L θ bN * ((MulAut.conj (θ (QuotientGroup.mk ℓ)))⁻¹ * ggLAut L θ hN') := hc
      rw [hc']; group
    exact mem_centralizer_of_ggLAut_eq_one L θ hL h1
  have hgFY := mem_sup_of_comm_mem_centralizer hS hN hgH hcomm
  have : h = (ℓ : G) * g := by rw [hg]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ℓ.2))
    (SetLike.le_def.mp (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hgFY)

theorem card_bstar_eq {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) :
    Nat.card Bs = Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxN : zpowers x ≤ Subgroup.normalizer (B₁ : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun b hb => (hBcomm b hb.1 x hxBs)))
  apply le_antisymm
  · have h1 : Nat.card ((B₁ : Set G) * (zpowers x : Set G)) ≤ Nat.card B₁ * Nat.card (zpowers x) :=
      Set.natCard_mul_le
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left B₁ (zpowers x) hxN, ← h43.2,
      Nat.card_zpowers, hxo] at h1
    exact h1
  · have hle : B₁ ≤ Bs := inf_le_left
    have hc := (B₁.subgroupOf Bs).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hc
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hBst.2.1)
    have hdvd : (B₁.subgroupOf Bs).index ∣ p ^ k := by
      rw [← hk]; exact Subgroup.index_dvd_card _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.index_eq_one] at hi
      apply h43.1
      have : (⟨x, hxBs⟩ : Bs) ∈ B₁.subgroupOf Bs := by rw [hi]; exact Subgroup.mem_top _
      exact this
    rw [← hc, hi]
    exact Nat.mul_le_mul_left _ (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hi0))

theorem exists_monoidHom_of_irredTableB (hF : GGL48NbrFieldInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hKG : GGIrredTableB p R I) (hp4 : ¬ p ∣ 4) :
    ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = zpowers x :=
    le_antisymm (GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1) (zpowers_le.mpr ⟨hxBs, hxC⟩)
  obtain ⟨hcard, hirr⟩ := hKG G L Bs θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3)
  rw [hCx, Nat.card_zpowers, hxo, card_bstar_eq hS] at hcard
  have hm : Nat.card B₁ = p ^ 4 := by
    exact Nat.eq_of_mul_eq_mul_right hp.pos hcard
  have h1 := ggL48AutomizerFirst_of_nbrField hF hS h46
  refine exists_monoidHom_of_irreducible hS h46 (A := ggL48H0 x U₁) inf_le_right ?_ hm hp4
  intro M hMB hM1 hMA
  set S := M ⊔ zpowers x with hSdef
  have hMx : zpowers x ≤ Subgroup.normalizer (M : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun m hm => hBcomm m (hMB hm).1 x hxBs))
  have hSBs : S ≤ Bs := sup_le (hMB.trans inf_le_left) (zpowers_le.mpr hxBs)
  have hNS : ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G) ≤
      Subgroup.normalizer (S : Set G) := by
    apply sup_le
    · intro a ha
      apply Subgroup.inf_normalizer_le_normalizer_sup M (zpowers x)
      exact ⟨GGL48TW.Cent.mem_normalizer_of_conj_mem (hMA a ha),
        Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          have hxa : Commute x a := by
            have := mem_centralizer_singleton_iff.mp ha.1
            first | exact this | exact this.symm
          exact (Commute.zpow_left hxa k).eq)⟩
    · intro c hc
      apply GGL48TW.Cent.mem_normalizer_of_conj_mem
      intro s hs
      have := (mem_centralizer_iff.mp hc) s (hSBs hs)
      rw [← this]; simpa using hs
  have hSN : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    intro n hn s hs
    exact (mem_normalizer_iff.mp (hNS (h1 ⟨hLx hn.1, hn.2⟩)) s).mp hs
  rw [hCx] at hirr
  rcases hirr S le_sup_right hSBs hSN with h | h
  · exfalso
    apply hM1
    rw [eq_bot_iff]
    intro m hm
    have hmx : m ∈ zpowers x := h ▸ (le_sup_left : M ≤ S) hm
    exact Subgroup.mem_bot.mpr (GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hmx (hMB hm))
  · apply Subgroup.eq_of_le_of_card_ge hMB
    have h2 : Nat.card ((M : Set G) * (zpowers x : Set G)) ≤ Nat.card M * Nat.card (zpowers x) :=
      Set.natCard_mul_le
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M (zpowers x) hMx, ← hSdef, h,
      Nat.card_zpowers, hxo] at h2
    change Nat.card Bs ≤ _ at h2
    rw [card_bstar_eq hS] at h2
    exact Nat.le_of_mul_le_mul_right h2 hp.pos

theorem quot_at_of_cent (hF : GGL48NbrFieldInput) (hcyc : GGL46CyclicIOneInput)
    (hW : GGL48HomocyclicOrMetaInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) (h46 : GGL46 p Bs x X U U₁)
    (R : Subgroup G) (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hUR : U ≤ R) (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁) :
    ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  by_cases hcov : Subgroup.normalizer (U₁ : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)
  · exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
      (not_mem_commutator_of_cover hS h46 hRp hRmax hA hcent hcov)
  have hhom : ¬ GGL48Homocyclic p U₁ := fun hhom =>
    hcov (normalizer_le_sup_of_homocyclic hS h46 hRp hRmax hA hhom)
  by_cases hind : p ∣ (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G))
  swap
  · exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
      (not_mem_commutator_of_not_dvd_relIndex' hS h46 hRp hRmax hA hcent hind)
  by_cases hnorm : ((ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).subgroupOf
      (Subgroup.normalizer (U₁ : Set G))).Normal
  · exact exists_monoidHom_of_normal hS h46 hRp hRmax hA hhom hind hnorm
  have hle := relIndex_le_of_not_homocyclic hS h46 hRp hRmax hA hhom
  have hpos : 0 < (ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)).relIndex
      (Subgroup.normalizer (U₁ : Set G)) :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have heq := le_antisymm hle (Nat.le_of_dvd hpos hind)
  by_cases hcop : p ∣ (ggL48H0 x U₁ ⊓ Subgroup.centralizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)).relIndex (ggL48H0 x U₁)
  · rcases hW G p B Bs x L D J X B₂ d y K U U₁ hS hI1 h46 with hh | hM
    · exact absurd hh hhom
    · exact frobeniusOuter_of_automizer_at hS h46 (hcyc G p B Bs x L D J X B₂ d y K U U₁ hS hI1)
        (ggL48AutomizerFirst_of_nbrField hF hS h46) hM
        R hRp hRmax hUR hA hcent hhom heq hnorm
  · exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
      (not_mem_commutator_of_frobenius hS h46 hRp hRmax hUR hA
        (hcyc G p B Bs x L D J X B₂ d y K U U₁ hS hI1) hcent heq hnorm hcop)

end CFSG.StandardType
