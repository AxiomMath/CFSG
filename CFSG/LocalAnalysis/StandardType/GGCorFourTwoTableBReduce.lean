module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGInnerDiagBound (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eb Eh : Subgroup (MulAut R), (Eb : Set (MulAut R)) ⊆ I → IsElemAbelian p Eb →
    p ^ r ≤ Nat.card Eb → p ^ 3 ≤ Nat.card Eb → Eb ≤ Eh → IsElemAbelian p Eh →
    Nat.card Eh ≤ p * Nat.card Eb → ¬ (Eh : Set (MulAut R)) ⊆ I →
    ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ Eh, ∀ u ∈ U, φ u ∈ U

@[expose] def GGNoTransvectionTorus (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eh : Subgroup (MulAut R), (Eh : Set (MulAut R)) ⊆ I → IsElemAbelian p Eh →
    p ^ r ≤ Nat.card Eh → p ^ 3 ≤ Nat.card Eh →
    ∀ a : Subgroup.normalizer (Eh : Set (MulAut R)),
      ¬ GGIsTransvection p (Eh.normalizerMonoidHom a)

section Config

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.bstar_le_normalizer {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) :
    Bs ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hT
  intro b hb
  refine mem_normalizer_of_sstar hS hnc ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (IsElemAbelian.comm hBs.2.1 hb (hBs.1 hS.2.1))

theorem card_range_ggBeta_bstar {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ hBsN).range ≤ p * Nat.card (ggBeta L θ hBN).range ∧
      p ^ 3 ≤ Nat.card (ggBeta L θ hBN).range ∧
      Nat.card (ggBeta L θ hBsN).range * p = Nat.card Bs := by
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have hcB := card_range_ggBeta_mul L θ hp hS hL hBN
  have hcE := card_range_ggBeta_mul_of hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
    hS.2.2.2.2 hL θ hBsN
  refine ⟨?_, ?_, hcE⟩
  · have h1 : Nat.card (ggBeta L θ hBsN).range * p ≤ p * Nat.card (ggBeta L θ hBN).range * p := by
      rw [hcE, mul_assoc, hcB]
      exact hBs.2.2.1
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  · have h := pow_four_le_card_of_bmax hp hS.1 hβ.2.2.2
    rw [← hcB, pow_succ] at h
    exact Nat.le_of_mul_le_mul_right h hp.pos

omit [Finite G] in
theorem range_ggBeta_le {L B Bs : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hBBs : B ≤ Bs) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ hBN).range ≤ (ggBeta L θ hBsN).range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b, hBBs b.2⟩, rfl⟩

omit [Finite G] in
theorem isElemAbelian_range_ggBeta {p : ℕ} {L E : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) : IsElemAbelian p (ggBeta L θ hEN).range :=
  isElemAbelian_range (fun a b => Subtype.ext (IsElemAbelian.comm hE a.2 b.2))
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) _

end Config

section InnerDiag

variable {G : Type} [Group G] [Finite G]

theorem bstar_innerDiag_of_bound {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hbound : GGInnerDiagBound p r R I) :
    Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  have hBsN := hC.bstar_le_normalizer hnc
  obtain ⟨hcard, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have hEbI : ((ggBeta L θ hBN).range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN h3 b
  have hEhI : ((ggBeta L θ hBsN).range : Set (MulAut R)) ⊆ I := by
    by_contra hnot
    obtain ⟨U, hU, hU2, hEU⟩ := hbound _ _ hEbI (isElemAbelian_range_ggBeta θ hS.1.1 hBN)
      (pow_le_card_range_ggBeta hp hS hL θ hBN hlift) h3' (range_ggBeta_le θ hBs.1 hBN hBsN)
      (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) hcard hnot
    obtain ⟨T, hTne, hT2, hBsT⟩ := exists_twoSubgroup_of_normalizes θ hBsN hU hU2
      (fun e he u hu => hEU _ ⟨⟨e, he⟩, rfl⟩ u hu)
    have hc := card_le_of_twoLocal hp ⟨T, hTne, hT2, rfl⟩ hBsT hBs.2.1
    rw [← hS.1.2.1] at hc
    have heq : B = Bs := Subgroup.eq_of_le_of_card_ge hBs.1 hc
    apply hnot
    rintro _ ⟨b, rfl⟩
    have hb : (b : G) ∈ B := heq ▸ b.2
    exact ggLAut_mem_of_induces L θ hBN h3 hb
  refine ⟨hBsN, fun b hb => ⟨_, ?_, largeEvenInduces_ggLAut_inv L θ (hBsN (Bs.inv_mem hb))⟩⟩
  exact hEhI ⟨⟨b⁻¹, Bs.inv_mem hb⟩, rfl⟩

theorem ggInnerDiagOnLab_bstar_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hM : GGInnerDiagOnLab S p B L) : GGInnerDiagOnLab S p Bs L := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  refine ⟨hL, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨hSl, hsplit, hBN, h3⟩, r, hlift, hbound⟩
  exact ⟨hs, hna, θ, hSl, hsplit, bstar_innerDiag_of_bound hC hnc hL θ hBN h3 hlift hbound⟩

end InnerDiag

theorem ggBstarInnerDiagLInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  exact ggInnerDiagOnLab_bstar_of_labels h hC (ggLNoncyclicInputOn_pilot G p B x L hC.1
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2⟩) hM)) hM

theorem ggBstarInnerDiagLInputOn_of_labels' {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) :
    GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  exact ggInnerDiagOnLab_bstar_of_labels h hC (ha₀ G p B x L hC.1) hM

section Transvection

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggLAut_conj {L : Subgroup G} {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (g b : Subgroup.normalizer (L : Set G)) :
    ggLAut L θ g * ggLAut L θ b * (ggLAut L θ g)⁻¹ = ggLAut L θ (g * b * g⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem isTransvection_of_center_ne {M : Type} [Group M] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} {Eh : Subgroup M} (hcomm : ∀ a b : ↥Bs, a * b = b * a)
    (f : ↥Bs →* ↥Eh) (hf : Function.Surjective f) (hker : Nat.card f.ker = p)
    {φ : MulAut ↥Bs} (hφ : GGIsTransvection p φ) (hφk : ∀ c ∈ f.ker, φ c = c)
    {ψ : MulAut ↥Eh} (hψ : ∀ c, ψ (f c) = f (φ c)) {b : ↥Bs} (hb : f (b⁻¹ * φ b) ≠ 1) :
    GGIsTransvection p ψ := by
  refine ⟨?_, ?_⟩
  swap
  · intro e
    obtain ⟨c, rfl⟩ := hf e
    rw [hψ, ← map_inv, ← map_mul, hψ, hφ.2 c]
  let δ : ↥Bs →* ↥Bs :=
    { toFun := fun c => c⁻¹ * φ c
      map_one' := by simp
      map_mul' := fun c c' => by
        rw [map_mul, mul_inv_rev, hcomm c'⁻¹ c⁻¹, mul_assoc, mul_assoc, ← mul_assoc c'⁻¹,
          hcomm c'⁻¹ (φ c), mul_assoc] }
  have hδ : ∀ c, δ c = c⁻¹ * φ c := fun _ => rfl
  have hδker : ∀ c, c ∈ δ.ker ↔ φ c = c := by
    intro c
    rw [MonoidHom.mem_ker, hδ, inv_mul_eq_one, eq_comm]
  have hH : Nat.card δ.ker * p = Nat.card ↥Bs := by
    rw [← hφ.1]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight hδker)
  have hBs0 : 0 < Nat.card ↥Bs := Nat.card_pos
  have hH0 : 0 < Nat.card δ.ker := Nat.card_pos
  have hδr : Nat.card δ.range = p := by
    have h1 := card_range_mul_card_ker δ
    rw [← hH, mul_comm (Nat.card δ.ker)] at h1
    exact Nat.eq_of_mul_eq_mul_right hH0 h1
  have hA : ∀ c, f (δ c) = 1 → δ c = 1 := by
    intro c hc
    by_contra hne
    have h1 : Subgroup.zpowers (δ c) ≤ f.ker := (Subgroup.zpowers_le).mpr hc
    have h2 : Subgroup.zpowers (δ c) ≤ δ.range := (Subgroup.zpowers_le).mpr ⟨c, rfl⟩
    have hcard : Nat.card (Subgroup.zpowers (δ c)) = p := by
      have hd := Subgroup.card_dvd_of_le h1
      rw [hker] at hd
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · exfalso
        apply hne
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
        exact h
      · exact h
    have e1 : Subgroup.zpowers (δ c) = f.ker :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, hker])
    have e2 : Subgroup.zpowers (δ c) = δ.range :=
      Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard, hδr])
    apply hb
    have : δ b ∈ f.ker := by
      rw [← e1, e2]
      exact ⟨b, rfl⟩
    exact this
  let F : ↥δ.ker →* ↥Eh := f.comp δ.ker.subtype
  have hFr : ∀ e : ↥Eh, e ∈ F.range ↔ ψ e = e := by
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      change ψ (f c) = f c
      rw [hψ, (hδker c).mp c.2]
    · intro he
      obtain ⟨c, rfl⟩ := hf e
      have h1 : f (δ c) = 1 := by
        rw [hδ, map_mul, map_inv, ← hψ, he, inv_mul_cancel]
      exact ⟨⟨c, hA c h1⟩, rfl⟩
  have hkle : f.ker ≤ δ.ker := fun c hc => (hδker c).mpr (hφk c hc)
  have hFk : Nat.card F.ker = p := by
    rw [← hker]
    refine Nat.card_congr
      { toFun := fun c => ⟨(c : ↥δ.ker), c.2⟩
        invFun := fun c => ⟨⟨c, hkle c.2⟩, c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcF := card_range_mul_card_ker F
  rw [hFk] at hcF
  have hcf := card_range_mul_card_ker f
  rw [hker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at hcf
  have hfix : Nat.card {e : ↥Eh // ψ e = e} = Nat.card F.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => (hFr e).symm)
  rw [hfix, hcF]
  have h2 : Nat.card δ.ker * p = Nat.card ↥Eh * p := by rw [hH, hcf]
  exact Nat.eq_of_mul_eq_mul_right hp.pos h2

theorem mem_zpowers_of_noTransvectionTorus {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (htv : GGNoTransvectionTorus p r R I)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφt : GGIsTransvection p φ) (b : ↥Bs) : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  by_contra hb0
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hC.2.1.1.trans hBsN
  obtain ⟨-, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  obtain ⟨g, hgx, hgN, hφg⟩ := hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  have hxBs : x ∈ Bs := hBs.1 hS.2.1
  set β := ggBeta L θ hBsN with hβdef
  set a : MulAut R := ggLAut L θ ⟨g, hgL⟩ with ha
  have hconj : ∀ c : ↥Bs, a * β c * a⁻¹ = β (φ c) := by
    intro c
    rw [ggBeta_eq, ggBeta_eq, ha, ggLAut_conj]
    congr 1
    apply Subtype.ext
    exact (hφg c).symm
  have hNa : a ∈ Subgroup.normalizer ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨φ c, (hconj c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      have h1 := hconj (φ.symm c)
      rw [MulEquiv.apply_symm_apply, hc] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hEhI : ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨c, rfl⟩
    exact ggBeta_mem L θ hBsN h3 c
  have hle := Subgroup.card_le_of_le (range_ggBeta_le θ hBs.1 hBN hBsN)
  refine htv β.range hEhI (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN)
    ((pow_le_card_range_ggBeta hp hS hL θ hBN hlift).trans hle) (h3'.trans hle) ⟨a, hNa⟩ ?_
  have hkerβ : β.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_ggBeta_of hp hBs.2.1 hxBs hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hL θ hBsN
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  refine isTransvection_of_center_ne hp (fun c c' => Subtype.ext (IsElemAbelian.comm hBs.2.1 c.2
    c'.2)) β.rangeRestrict β.rangeRestrict_surjective ?_ hφt ?_ ?_ (b := b) ?_
  · rw [hkerβ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2.1.2 x hxBs) hS.2.2.1]
  · intro c hc
    rw [hkerβ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  · intro c
    exact Subtype.ext (hconj c)
  · intro h1
    apply hb0
    have h2 : b⁻¹ * φ b ∈ β.rangeRestrict.ker := h1
    rw [hkerβ, Subgroup.mem_subgroupOf] at h2
    exact h2

end Transvection

theorem ggLTransvectionCenterInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGNoTransvectionTorus p r R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hC.1 (largeEvenMarking_mono
    (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1,
      fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hM)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionTorus hC hnc hL θ hBsN h3 hlift htvt hφ htv b

theorem ggLTransvectionCenterInputOn_of_labels' {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGNoTransvectionTorus p r R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionTorus hC (ha₀ G p B x L hC.1) hL θ hBsN h3 hlift htvt hφ
    htv b

end CFSG.StandardType
