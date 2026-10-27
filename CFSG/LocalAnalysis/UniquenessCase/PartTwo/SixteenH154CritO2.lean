module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_not_dvd_inf_conjSubgroup {K : Subgroup G} {q : ℕ}
    (h : CFSG.RankThree.PartOne.IsStronglyPEmbedded q K) {g : G} (hg : g ∉ K) :
    ¬ q ∣ Nat.card ↥(K ⊓ conjSubgroup K g) :=
  h.2.2 g⁻¹ fun h' => hg (inv_mem_iff.1 h')

theorem s16h_inf_conjSubgroup_eq_bot_of_strong {K : Subgroup G} (hK : rankThreeIsMaxTwoLocal K)
    {q : ℕ} (hsp : ∀ g : G, g ∉ K → ¬ q ∣ Nat.card ↥(K ⊓ conjSubgroup K g))
    {U₁ U₂ : Subgroup G} (h₁ : IsPGroup 2 U₁) (h₂ : IsPGroup 2 U₂)
    (hU₁ : ∀ u ∈ U₁, u ≠ 1 → UniqueMax K (K ⊓ centralizer ({u} : Set G)) ∨
      q ∣ Nat.card ↥(K ⊓ centralizer ({u} : Set G)))
    (hU₂ : ∀ w ∈ U₂, w ≠ 1 → UniqueMax K (K ⊓ centralizer ({w} : Set G))) {g : G}
    (hg : g ∉ K) : U₁ ⊓ conjSubgroup U₂ g = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxU₁, hxU₂⟩ := Subgroup.mem_inf.mp hx
  have hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := h₁ ⟨x, hxU₁⟩
    exact ⟨n, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn⟩
  have hw'U₂ : g * x * g⁻¹ ∈ U₂ := mem_conjSubgroup_iff.mp hxU₂
  have hw'1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have hconj : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hconj, h]
    simp
  have hw'2 : ∃ n : ℕ, (g * x * g⁻¹) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := h₂ ⟨g * x * g⁻¹, hw'U₂⟩
    exact ⟨n, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn⟩
  have hcentw' : centralizer ({g * x * g⁻¹} : Set G) ≤ K :=
    (centralizer_le_of_uniqueMax hK hw'1 hw'2 (hU₂ _ hw'U₂ hw'1)).1
  have hle : K ⊓ centralizer ({x} : Set G) ≤ K ⊓ conjSubgroup K g := by
    intro y hy
    obtain ⟨hyK, hycent⟩ := Subgroup.mem_inf.mp hy
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hycent
    refine Subgroup.mem_inf.2 ⟨hyK, ?_⟩
    rw [mem_conjSubgroup_iff]
    apply hcentw'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * (g * x * g⁻¹)
        = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  rcases hU₁ x hxU₁ hx1 with hu | hdvd
  · exact (centralizer_le_of_uniqueMax hK hx1 hx2 hu).2 g hg (hle.trans inf_le_right)
  · exact hsp g hg (hdvd.trans (Subgroup.card_dvd_of_le hle))

private theorem s16h_centSub_commSub_conj {W : Type} [CommGroup W]
    (L : Subgroup (MulAut W)) (φ : MulAut W) :
    (centSub (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom))).map
        (MulAut.conj φ⁻¹).toMonoidHom =
      centSub (commSub (⊤ : Subgroup W) L) := by
  have hcomm : commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom) =
      (commSub (⊤ : Subgroup W) L).map φ.toMonoidHom :=
    s15_Infra_commSub_top_map_conj L φ
  ext x
  rw [Subgroup.mem_map_equiv (f := MulAut.conj φ⁻¹)
      (K := centSub (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom))),
    mem_centSub, mem_centSub]
  simp only [MulAut.conj_symm_apply, inv_inv]
  constructor
  · intro h v hv
    have hv' : φ v ∈ commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom) := by
      rw [hcomm]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hv
    have h1 : (φ * x * φ⁻¹) (φ v) = φ v := h (φ v) hv'
    have h2 : φ (x v) = φ v := by
      simpa [MulAut.mul_apply, MulAut.inv_apply_self] using h1
    exact φ.injective h2
  · intro h u hu
    rw [hcomm] at hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    show (φ * x * φ⁻¹) (φ v) = φ v
    simpa [MulAut.mul_apply, MulAut.inv_apply_self] using congrArg φ (h v hv)

theorem s16h_blockBound_conj {W : Type} [CommGroup W] {A L : Subgroup (MulAut W)} {q c : ℕ}
    (h : s16h_BlockBound A L q c) {φ : MulAut W} (hφ : φ ∈ A) :
    s16h_BlockBound A (L.map (MulAut.conj φ).toMonoidHom) q c := by
  intro E hE hEab
  have hφinv : φ⁻¹ ∈ A := A.inv_mem hφ
  let E' : Subgroup (MulAut W) := E.map (MulAut.conj φ⁻¹).toMonoidHom
  have hinj : Function.Injective (MulAut.conj φ⁻¹).toMonoidHom :=
    (MulAut.conj φ⁻¹).injective
  have hE'le : E' ≤ A ⊓ normalizer (L : Set (MulAut W)) := by
    intro x' hx'
    change x' ∈ E.map (MulAut.conj φ⁻¹).toMonoidHom at hx'
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
    rw [← hxy]
    change (MulAut.conj φ⁻¹) y ∈ A ⊓ normalizer (L : Set (MulAut W))
    have hyA : y ∈ A := (hE hy).1
    have hyN : y ∈ normalizer (L.map (MulAut.conj φ).toMonoidHom : Set (MulAut W)) :=
      (hE hy).2
    have hx'_eq : (MulAut.conj φ⁻¹) y = φ⁻¹ * y * φ := by
      rw [MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hx'_eq]
      exact A.mul_mem (A.mul_mem hφinv hyA) hφ
    · rw [Subgroup.mem_normalizer_iff]
      intro l
      have hiff1 : l ∈ L ↔ MulAut.conj φ l ∈ L.map (MulAut.conj φ).toMonoidHom := by
        rw [Subgroup.mem_map_equiv (f := MulAut.conj φ) (K := L),
          MulEquiv.symm_apply_apply]
      have hconjkey : (MulAut.conj φ).symm (y * MulAut.conj φ l * y⁻¹) =
          (MulAut.conj φ⁻¹) y * l * ((MulAut.conj φ⁻¹) y)⁻¹ := by
        rw [MulAut.conj_symm_apply, MulAut.conj_apply, hx'_eq]
        group
      have hiff2 : y * MulAut.conj φ l * y⁻¹ ∈ L.map (MulAut.conj φ).toMonoidHom ↔
          (MulAut.conj φ⁻¹) y * l * ((MulAut.conj φ⁻¹) y)⁻¹ ∈ L := by
        rw [Subgroup.mem_map_equiv (f := MulAut.conj φ) (K := L), hconjkey]
      have hnorm : MulAut.conj φ l ∈ L.map (MulAut.conj φ).toMonoidHom ↔
          y * MulAut.conj φ l * y⁻¹ ∈ L.map (MulAut.conj φ).toMonoidHom :=
        (Subgroup.mem_normalizer_iff.mp hyN) (MulAut.conj φ l)
      rw [hiff1, hnorm, hiff2]
  have hE'ab : IsElemAbelian q E' := hEab.map (MulAut.conj φ⁻¹).toMonoidHom
  have hstep := h E' hE'le hE'ab
  have hcardE : Nat.card ↥E' = Nat.card ↥E := Subgroup.card_map_of_injective hinj
  have hcent := s16h_centSub_commSub_conj L φ
  have hinf : E' ⊓ centSub (commSub (⊤ : Subgroup W) L) =
      (E ⊓ centSub (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom))).map
        (MulAut.conj φ⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf E
      (centSub (commSub (⊤ : Subgroup W) (L.map (MulAut.conj φ).toMonoidHom)))
      (MulAut.conj φ⁻¹).toMonoidHom hinj, hcent]
  have hcardC : Nat.card ↥(E' ⊓ centSub (commSub (⊤ : Subgroup W) L)) =
      Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W)
        (L.map (MulAut.conj φ).toMonoidHom))) := by
    rw [hinf]
    exact Subgroup.card_map_of_injective hinj
  rw [hcardE, hcardC] at hstep
  exact hstep

theorem s16h_card_le_of_two_blocks {W : Type} [CommGroup W] [Finite W]
    {A L₁ L₂ : Subgroup (MulAut W)} {q c₁ c₂ : ℕ} (h₁ : s16h_BlockBound A L₁ q c₁)
    (h₂ : s16h_BlockBound A L₂ q c₂) {E : Subgroup (MulAut W)} (hEA : E ≤ A)
    (hE₁ : E ≤ normalizer (L₁ : Set (MulAut W))) (hE₂ : E ≤ normalizer (L₂ : Set (MulAut W)))
    (hE : IsElemAbelian q E) :
    Nat.card ↥E ≤ q ^ (c₁ + c₂) *
      Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L₁ ⊔ commSub (⊤ : Subgroup W) L₂)) := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  set E' := E ⊓ centSub (commSub (⊤ : Subgroup W) L₁) with hE'
  have hE'le : E' ≤ E := inf_le_left
  have step1 := h₁ E (le_inf hEA hE₁) hE
  have step2 := h₂ E' (le_inf (hE'le.trans hEA) (hE'le.trans hE₂)) (hE.mono hE'le)
  have hsub : E' ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ≤
      E ⊓ centSub (commSub (⊤ : Subgroup W) L₁ ⊔ commSub (⊤ : Subgroup W) L₂) := by
    rintro x ⟨⟨hxE, hx1⟩, hx2⟩
    exact ⟨hxE, s16h_centSub_inf_le_centSub_sup _ _ ⟨hx1, hx2⟩⟩
  calc Nat.card ↥E ≤ q ^ c₁ * Nat.card ↥E' := step1
    _ ≤ q ^ c₁ * (q ^ c₂ * Nat.card ↥(E' ⊓ centSub (commSub (⊤ : Subgroup W) L₂))) :=
        Nat.mul_le_mul_left _ step2
    _ ≤ q ^ c₁ * (q ^ c₂ * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L₁ ⊔
        commSub (⊤ : Subgroup W) L₂))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hsub))
    _ = q ^ (c₁ + c₂) * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L₁ ⊔
        commSub (⊤ : Subgroup W) L₂)) := by rw [pow_add, mul_assoc]

theorem s16h_le_stabTil {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    D.M ≤ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

theorem s16h_barSub_le_normalizer_of_le_nBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {L E : Subgroup G} (hE : E ≤ nBar M V₀ V hV L) :
    barSub V₀ V hV E ≤ normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  refine (barSub_mono V₀ V hV hE).trans ?_
  unfold nBar
  rw [barSub_preBarSub]
  exact inf_le_left

theorem s16h_card_le_three_mul_card_inf_nBar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V h.isElemAbelian L ≤ 3) {E : Subgroup G}
    (hEM : E ≤ D.M) :
    Nat.card ↥E ≤ 3 * Nat.card ↥(E ⊓ nBar D.M V₀ V h.isElemAbelian L) := by
  have hV := h.isElemAbelian
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  refine s16h_card_le_mul_card_preBarSub hV hEM (hEM.trans (s16h_le_stabTil h)) _ ?_
  refine s16h_card_le_three_mul_card_inf_normalizer hs ?_
    (L := barSub V₀ V hV L) ⟨1, (Mbar D.M V₀ V hV).one_mem, (s15GapFour_map_conj_one _).symm⟩
  rintro x hx T ⟨φ, hφ, rfl⟩
  exact ⟨x * φ, (Mbar D.M V₀ V hV).mul_mem (barSub_mono V₀ V hV hEM hx) hφ,
    (s15GapFour_map_conj_mul _ x φ).symm⟩

theorem s16h_barSub_inf_nBar_le_normalizer_conj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V h.isElemAbelian L = 3) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian q E)
    {T : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hT : T ∈ conjSetOf (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L)) :
    barSub V₀ V h.isElemAbelian (E ⊓ nBar D.M V₀ V h.isElemAbelian L) ≤
      normalizer (T : Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  have hV := h.isElemAbelian
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  intro φ hφ
  have hφE : φ ∈ barSub V₀ V hV E := barSub_mono V₀ V hV inf_le_left hφ
  have hφM : φ ∈ Mbar D.M V₀ V hV := barSub_mono V₀ V hV (inf_le_left.trans hEM) hφ
  have hφn : φ ∈ normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    s16h_barSub_le_normalizer_of_le_nBar D.M V₀ V hV inf_le_right hφ
  exact uc22r899_mem_normalizer_of_fix (M := Mbar D.M V₀ V hV) (L := barSub V₀ V hV L) hs hφM
    hq hq2 (k := 1) (by rw [pow_one]; exact (s16h_barSub_isElemAbelian hV hE).2 φ hφE)
    (fun _ => ⟨barSub V₀ V hV L, ⟨1, (Mbar D.M V₀ V hV).one_mem,
      (s15GapFour_map_conj_one _).symm⟩, hφn⟩) T hT

theorem s16h_card_le_sq_mul_card_inf_preBarSub_sup (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V h.isElemAbelian L = 3) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L) q 1)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian q E) {x y : G} (hx : x ∈ D.M)
    (hy : y ∈ D.M) :
    Nat.card ↥E ≤ 3 * (q ^ 2 * Nat.card ↥((E ⊓ nBar D.M V₀ V h.isElemAbelian L) ⊓
      preBarSub D.M V₀ V h.isElemAbelian (centSub (wTil V₀ V h.isElemAbelian (conjSubgroup L x) ⊔
        wTil V₀ V h.isElemAbelian (conjSubgroup L y))))) := by
  have hV := h.isElemAbelian
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hMs := s16h_le_stabTil h
  have hconj : ∀ m ∈ D.M, barSub V₀ V hV (conjSubgroup L m) ∈
      conjSetOf (Mbar D.M V₀ V hV) (barSub V₀ V hV L) := fun m hm =>
    ⟨(actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹, (Mbar D.M V₀ V hV).inv_mem
      (actTil_mem_barSub V₀ V hV hm (hMs hm)), s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L⟩
  have hBBm : ∀ m ∈ D.M, s16h_BlockBound (Mbar D.M V₀ V hV) (barSub V₀ V hV (conjSubgroup L m))
      q 1 := fun m hm => by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L]
    exact s16h_blockBound_conj hBB ((Mbar D.M V₀ V hV).inv_mem
      (actTil_mem_barSub V₀ V hV hm (hMs hm)))
  have hE₁M : E ⊓ nBar D.M V₀ V hV L ≤ D.M := inf_le_left.trans hEM
  have hE₁ab : IsElemAbelian q (E ⊓ nBar D.M V₀ V hV L) := hE.mono inf_le_left
  have hbar := s16h_card_le_of_two_blocks (hBBm x hx) (hBBm y hy)
    (barSub_mono V₀ V hV hE₁M)
    (s16h_barSub_inf_nBar_le_normalizer_conj D h hs hq hq2 hEM hE (hconj x hx))
    (s16h_barSub_inf_nBar_le_normalizer_conj D h hs hq hq2 hEM hE (hconj y hy))
    (s16h_barSub_isElemAbelian hV hE₁ab)
  have hK1 := s16h_card_le_mul_card_preBarSub hV hE₁M (hE₁M.trans hMs) _ hbar
  calc Nat.card ↥E ≤ 3 * Nat.card ↥(E ⊓ nBar D.M V₀ V hV L) :=
        s16h_card_le_three_mul_card_inf_nBar D h hs.le hEM
    _ ≤ 3 * (q ^ (1 + 1) * _) := Nat.mul_le_mul_left _ hK1

theorem s16h_dvd_card_cent_of_cElt (D : Data G) (h127 : R127 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {P : Subgroup G} {w : G}
    (hwV : w ∈ V) (hwV₀ : w ∉ V₀) (hP : P ≤ F11.CElt D.M V₀ w) (hqP : q ∣ Nat.card ↥P) :
    q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V (Hyp125.hyp11 h127 h.hyp125)
    (s16c34_card_v0_le_four D h) w hwV hwV₀
  have hmul := Subgroup.relIndex_mul_card (H := D.M ⊓ centralizer ({w} : Set G))
    (K := F11.CElt D.M V₀ w)
  rw [hn] at hmul
  have hqC : q ∣ 2 ^ n * Nat.card ↥(D.M ⊓ centralizer ({w} : Set G) ⊓ F11.CElt D.M V₀ w) := by
    rw [hmul]
    exact hqP.trans (Subgroup.card_dvd_of_le hP)
  have hq2n : ¬ q ∣ 2 ^ n := fun hdvd =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))
  exact ((hq.dvd_mul.1 hqC).resolve_left hq2n).trans
    (Subgroup.card_dvd_of_le inf_le_left)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
