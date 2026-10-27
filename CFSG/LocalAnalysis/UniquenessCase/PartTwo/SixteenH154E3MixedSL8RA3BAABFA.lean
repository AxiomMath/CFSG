module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABFAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s16h_sl28_kbar_two (D : Data G) (V L : Subgroup G) (x : G)
    (hV : IsElemAbelian 2 V) : Subgroup (MulAut (Vtil ⊥ V hV)) :=
  Mbar D.M ⊥ V hV ⊓
    Subgroup.centralizer ((lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _) ⊓
    Subgroup.centralizer
      ((barSub ⊥ V hV (conjSubgroup L x) : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _)

private theorem s16h_sl28_barSub_map_conj_mem (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφ : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) :
    (lBar ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
        lBar ⊥ V h.hyp151.isElemAbelian L ∨
      (lBar ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub ⊥ V h.hyp151.isElemAbelian D.M φ).1 hφ
  have hm : (g : G)⁻¹ ∈ stabTil ⊥ V :=
    (stabTil ⊥ V).inv_mem g.2
  have hg_inv : (⟨(g : G)⁻¹, hm⟩ : stabTil ⊥ V) = g⁻¹ :=
    Subtype.ext rfl
  have hbar := s15_Infra_barSub_conjSubgroup ⊥ V h.hyp151.isElemAbelian hm L
  rw [hg_inv] at hbar
  rw [show actTil ⊥ V h.hyp151.isElemAbelian g⁻¹ =
      (actTil ⊥ V h.hyp151.isElemAbelian g)⁻¹ from
        map_inv (actTil ⊥ V h.hyp151.isElemAbelian) (g : stabTil ⊥ V)] at hbar
  rw [inv_inv, hgφ] at hbar
  have hgMinv : (g : G)⁻¹ ∈ D.M := D.M.inv_mem hgM
  rcases c23_barSub_conj_cases D h.hyp151 h.hyp151.isElemAbelian hs2 hxM hxn hgMinv with
    hc | hc
  · left
    show (barSub ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
      barSub ⊥ V h.hyp151.isElemAbelian L
    rw [← hbar, hc]
  · right
    show (barSub ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)
    rw [← hbar, hc]

theorem s16h_sl28_wTil_sup_conj_eq_top
    (D : Data G) (S : s16h_Std D)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊔
      wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) = ⊤ := by
  have hle : (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)) ≤
      commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊔
        wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
    refine le_trans (le_of_eq hW.1.symm) ?_
    refine iSup_le fun X => iSup_le fun hX => ?_
    obtain ⟨φ, hφ, rfl⟩ := hX
    rcases s16h_sl28_barSub_map_conj_mem D h hs2 hxM hxn hφ with hc | hc
    · rw [← s15_Infra_commSub_top_map_conj
        (lBar ⊥ V h.hyp151.isElemAbelian L) φ, hc]
      exact le_sup_left
    · rw [← s15_Infra_commSub_top_map_conj
        (lBar ⊥ V h.hyp151.isElemAbelian L) φ, hc]
      exact le_sup_right
  exact le_antisymm le_top hle

private theorem s16h_sl28_kbar_le_stab_wTil
    (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V) (x : G) :
    s16h_sl28_kbar_two D V L x hV ≤
      stabSub (commSub ⊤ (lBar ⊥ V hV L)) := by
  intro a ha
  have hcen : a ∈ Subgroup.centralizer
      ((lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _) := ha.1.2
  have hmem : a ∈ Subgroup.normalizer
      ((lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _) :=
    Subgroup.centralizer_le_normalizer _ hcen
  have hmap : (lBar ⊥ V hV L).map (MulAut.conj a).toMonoidHom = lBar ⊥ V hV L :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hmem
  have hWmap : (commSub ⊤ (lBar ⊥ V hV L)).map a.toMonoidHom = commSub ⊤ (lBar ⊥ V hV L) := by
    have h := s15_Infra_commSub_top_map_conj (lBar ⊥ V hV L) a
    rw [hmap] at h
    exact h.symm
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : a u ∈ (commSub ⊤ (lBar ⊥ V hV L)).map a.toMonoidHom := by rwa [hWmap]
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp h1
    exact a.injective hw' ▸ hw
  · intro hu
    have h1 : a u ∈ (commSub ⊤ (lBar ⊥ V hV L)).map a.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hWmap] at h1

private theorem s16h_sl28_kbar_le_stab_wxTil
    (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V) (x : G) :
    s16h_sl28_kbar_two D V L x hV ≤
      stabSub (commSub ⊤ (barSub ⊥ V hV (conjSubgroup L x))) := by
  intro a ha
  have hcen : a ∈ Subgroup.centralizer
      ((barSub ⊥ V hV (conjSubgroup L x) : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _) := ha.2
  have hmem : a ∈ Subgroup.normalizer
      ((barSub ⊥ V hV (conjSubgroup L x) : Subgroup (MulAut (Vtil ⊥ V hV))) : Set _) :=
    Subgroup.centralizer_le_normalizer _ hcen
  have hmap : (barSub ⊥ V hV (conjSubgroup L x)).map (MulAut.conj a).toMonoidHom =
      barSub ⊥ V hV (conjSubgroup L x) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hmem
  have hWmap : (commSub ⊤ (barSub ⊥ V hV (conjSubgroup L x))).map a.toMonoidHom =
      commSub ⊤ (barSub ⊥ V hV (conjSubgroup L x)) := by
    have h := s15_Infra_commSub_top_map_conj (barSub ⊥ V hV (conjSubgroup L x)) a
    rw [hmap] at h
    exact h.symm
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : a u ∈ (commSub ⊤ (barSub ⊥ V hV (conjSubgroup L x))).map a.toMonoidHom := by
      rwa [hWmap]
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp h1
    exact a.injective hw' ▸ hw
  · intro hu
    have h1 : a u ∈ (commSub ⊤ (barSub ⊥ V hV (conjSubgroup L x))).map a.toMonoidHom :=
      ⟨u, hu, rfl⟩
    rwa [hWmap] at h1

private theorem s16h_sl28_pow_seven_mem_centSub {Vt : Type} [CommGroup Vt]
    (K : Subgroup (MulAut Vt)) (W : Subgroup Vt) (C : Subgroup (MulAut Vt))
    (hK : K ≤ stabSub W) (hKC : K ≤ Subgroup.centralizer (C : Set (MulAut Vt)))
    (hcard : Nat.card ↥(autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W) ∣ 7)
    {a : MulAut Vt} (ha : a ∈ K) : a ^ 7 ∈ centSub W := by
  have hle : autSub K W ≤ autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W :=
    autSub_mono hKC W
  have haW : a ∈ stabSub W := hK ha
  let a₁ : MulAut W := resHom W ⟨a, haW⟩
  have ha₁ : a₁ ∈ autSub K W := mem_autSub.mpr ⟨⟨a, haW⟩, ha, rfl⟩
  have ha₁7 : a₁ ^ 7 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (Subgroup.orderOf_dvd_natCard (autSub K W) ha₁)
        (dvd_trans (Subgroup.card_dvd_of_le hle) hcard))
  have ha7W : a ^ 7 ∈ stabSub W := (stabSub W).pow_mem haW 7
  have hres : resHom W ⟨a ^ 7, ha7W⟩ = a₁ ^ 7 := by
    have h1 : (⟨a ^ 7, ha7W⟩ : stabSub W) = ⟨a, haW⟩ ^ 7 := Subtype.ext rfl
    rw [h1, map_pow]
  refine mem_centSub.mpr fun v hv => ?_
  have h1 : (resHom W ⟨a ^ 7, ha7W⟩) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    rw [hres, ha₁7]
    rfl
  have h2 := congrArg (fun w : W => (w : Vt)) h1
  rw [resHom_apply] at h2
  exact h2

private theorem s16h_sl28_commutator_mem_centSub {Vt : Type} [CommGroup Vt]
    (K : Subgroup (MulAut Vt)) (W : Subgroup Vt) (C : Subgroup (MulAut Vt))
    (hK : K ≤ stabSub W) (hKC : K ≤ Subgroup.centralizer (C : Set (MulAut Vt)))
    (hcard : Nat.card ↥(autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W) ∣ 7)
    {a b : MulAut Vt} (ha : a ∈ K) (hb : b ∈ K) : a * b * a⁻¹ * b⁻¹ ∈ centSub W := by
  have hle : autSub K W ≤ autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W :=
    autSub_mono hKC W
  have haW : a ∈ stabSub W := hK ha
  have hbW : b ∈ stabSub W := hK hb
  let a₁ : MulAut W := resHom W ⟨a, haW⟩
  let b₁ : MulAut W := resHom W ⟨b, hbW⟩
  have ha₁ : a₁ ∈ autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W :=
    hle (mem_autSub.mpr ⟨⟨a, haW⟩, ha, rfl⟩)
  have hb₁ : b₁ ∈ autSub (Subgroup.centralizer (C : Set (MulAut Vt))) W :=
    hle (mem_autSub.mpr ⟨⟨b, hbW⟩, hb, rfl⟩)
  have hcomm : a₁ * b₁ = b₁ * a₁ :=
    Subtype.ext_iff.mp (s16h_commute_of_card_dvd_seven hcard ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩)
  have hcW : a * b * a⁻¹ * b⁻¹ ∈ stabSub W :=
    (stabSub W).mul_mem
      ((stabSub W).mul_mem ((stabSub W).mul_mem haW hbW) ((stabSub W).inv_mem haW))
      ((stabSub W).inv_mem hbW)
  have hres : resHom W ⟨a * b * a⁻¹ * b⁻¹, hcW⟩ = 1 := by
    have h1 : resHom W ⟨a * b * a⁻¹ * b⁻¹, hcW⟩ = a₁ * b₁ * a₁⁻¹ * b₁⁻¹ := by
      rw [show (⟨a * b * a⁻¹ * b⁻¹, hcW⟩ : stabSub W) =
          ⟨a, haW⟩ * ⟨b, hbW⟩ * ⟨a, haW⟩⁻¹ * ⟨b, hbW⟩⁻¹ by
        apply Subtype.ext; rfl]
      simp only [map_mul, map_inv]
      rfl
    rw [h1, hcomm]
    group
  refine mem_centSub.mpr fun v hv => ?_
  have h1 : (resHom W ⟨a * b * a⁻¹ * b⁻¹, hcW⟩) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    rw [hres]
    rfl
  have h2 := congrArg (fun w : W => (w : Vt)) h1
  rw [resHom_apply] at h2
  exact h2

private theorem s16h_sl28_eq_one_of_mem_centSub_sup {Vt : Type} [CommGroup Vt]
    {W Wx : Subgroup Vt} (hsup : W ⊔ Wx = ⊤)
    {c : MulAut Vt} (hW : c ∈ centSub W) (hWx : c ∈ centSub Wx) : c = 1 := by
  have hfixW : W ≤ fixV (Subgroup.zpowers c) :=
    fun v hv => mem_fixV_zpowers_iff_apply.mpr ((mem_centSub.mp hW) v hv)
  have hfixWx : Wx ≤ fixV (Subgroup.zpowers c) :=
    fun v hv => mem_fixV_zpowers_iff_apply.mpr ((mem_centSub.mp hWx) v hv)
  have htop : (⊤ : Subgroup Vt) ≤ fixV (Subgroup.zpowers c) := by
    rw [← hsup]
    exact sup_le hfixW hfixWx
  refine MulEquiv.ext fun v => ?_
  simpa using mem_fixV_zpowers_iff_apply.mp (htop (Subgroup.mem_top v))

theorem s16h_sl28_kbar_two_abelian_exp_seven
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    (∀ a ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian, a ^ 7 = 1) ∧
      (∀ a ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian,
        ∀ b ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian, a * b = b * a) := by
  classical
  let hV := h.hyp151.isElemAbelian
  let Vt := Vtil ⊥ V hV
  let A : Subgroup (MulAut Vt) := lBar ⊥ V hV L
  let B : Subgroup (MulAut Vt) := barSub ⊥ V hV (conjSubgroup L x)
  let W : Subgroup Vt := commSub ⊤ A
  let Wx : Subgroup Vt := commSub ⊤ B
  let K : Subgroup (MulAut Vt) := s16h_sl28_kbar_two D V L x hV
  have hcardA : Nat.card ↥(autSub (Subgroup.centralizer (A : Set (MulAut Vt))) W) ∣ 7 :=
    s16h_sl28_centralizer_aut_card_dvd_seven (W := Vt) (L := A)
      (s15_Infra_vtil_sq_eq_one ⊥ V hV) hrow
  have hcardB : Nat.card ↥(autSub (Subgroup.centralizer (B : Set (MulAut Vt))) Wx) ∣ 7 :=
    s16h_sl28_centralizer_aut_card_dvd_seven_conj D S h hrow hxM
  have hsup : W ⊔ Wx = ⊤ :=
    s16h_sl28_wTil_sup_conj_eq_top D S h hs2 ht hW hcomp hxM hxn
  have hKcenA : K ≤ Subgroup.centralizer (A : Set (MulAut Vt)) := by
    intro a ha
    exact ha.1.2
  have hKcenB : K ≤ Subgroup.centralizer (B : Set (MulAut Vt)) := by
    intro a ha
    exact ha.2
  have hKW : K ≤ stabSub W := s16h_sl28_kbar_le_stab_wTil D hV x
  have hKWx : K ≤ stabSub Wx := s16h_sl28_kbar_le_stab_wxTil D hV x
  constructor
  · intro a ha
    have h7W : a ^ 7 ∈ centSub W :=
      s16h_sl28_pow_seven_mem_centSub K W A hKW hKcenA hcardA ha
    have h7Wx : a ^ 7 ∈ centSub Wx :=
      s16h_sl28_pow_seven_mem_centSub K Wx B hKWx hKcenB hcardB ha
    exact s16h_sl28_eq_one_of_mem_centSub_sup hsup h7W h7Wx
  · intro a ha b hb
    have hcW : a * b * a⁻¹ * b⁻¹ ∈ centSub W :=
      s16h_sl28_commutator_mem_centSub K W A hKW hKcenA hcardA ha hb
    have hcWx : a * b * a⁻¹ * b⁻¹ ∈ centSub Wx :=
      s16h_sl28_commutator_mem_centSub K Wx B hKWx hKcenB hcardB ha hb
    have hc1 : a * b * a⁻¹ * b⁻¹ = 1 :=
      s16h_sl28_eq_one_of_mem_centSub_sup hsup hcW hcWx
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = 1 * (b * a) := by rw [hc1]
      _ = b * a := one_mul _

theorem s16h_sl28_tau_conj_kbar_two
    (D : Data G) (S : s16h_Std D)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτM : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hτN : τ ∉ Subgroup.normalizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)) (hτ2 : τ ^ 2 = 1) :
    ∀ a ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian,
      τ * a * τ⁻¹ ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian := by
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
  have hτinv : τ⁻¹ = τ := (eq_inv_of_mul_eq_one_right hττ).symm
  have hmapτ : (lBar ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj τ).toMonoidHom =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
    rcases s16h_sl28_barSub_map_conj_mem D h hs2 hxM hxn hτM with hc | hc
    · exact absurd ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hc) hτN
    · exact hc
  have hmapτB : (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)).map
      (MulAut.conj τ).toMonoidHom = lBar ⊥ V h.hyp151.isElemAbelian L := by
    have h := CFSG.Walter.map_conj_map_conj_inv τ (lBar ⊥ V h.hyp151.isElemAbelian L)
    rw [hmapτ] at h
    rwa [hτinv] at h
  intro a ha
  obtain ⟨⟨haM, haL⟩, haB⟩ := ha
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (Mbar D.M ⊥ V h.hyp151.isElemAbelian).mul_mem
      ((Mbar D.M ⊥ V h.hyp151.isElemAbelian).mul_mem hτM haM)
      ((Mbar D.M ⊥ V h.hyp151.isElemAbelian).inv_mem hτM)
  · change τ * a * τ⁻¹ ∈ Subgroup.centralizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)
    have haB' : a ∈ Subgroup.centralizer
        ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) : Subgroup _) : Set _) := haB
    have hle := Subgroup.map_centralizer_le_centralizer_image
      ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) : Subgroup _) : Set _)
      (MulAut.conj τ).toMonoidHom
    rw [← Subgroup.coe_map, hmapτB] at hle
    exact hle ⟨a, haB', by change MulAut.conj τ a = τ * a * τ⁻¹; rw [MulAut.conj_apply]⟩
  · change τ * a * τ⁻¹ ∈ Subgroup.centralizer
        ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) : Subgroup _) : Set _)
    have haL' : a ∈ Subgroup.centralizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) := haL
    have hle := Subgroup.map_centralizer_le_centralizer_image
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)
      (MulAut.conj τ).toMonoidHom
    rw [← Subgroup.coe_map, hmapτ] at hle
    exact hle ⟨a, haL', by change MulAut.conj τ a = τ * a * τ⁻¹; rw [MulAut.conj_apply]⟩

theorem s16h_sl28_tau_swaps_wTil
    (D : Data G) (S : s16h_Std D)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτM : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hτN : τ ∉ Subgroup.normalizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)) (hτ2 : τ ^ 2 = 1) :
    (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)).map τ.toMonoidHom =
        wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ∧
      (wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)).map τ.toMonoidHom =
        commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) := by
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
  have hτinv : τ⁻¹ = τ := (eq_inv_of_mul_eq_one_right hττ).symm
  have hmapτ : (lBar ⊥ V h.hyp151.isElemAbelian L).map (MulAut.conj τ).toMonoidHom =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
    rcases s16h_sl28_barSub_map_conj_mem D h hs2 hxM hxn hτM with hc | hc
    · exact absurd ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hc) hτN
    · exact hc
  have hmapτB : (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)).map
      (MulAut.conj τ).toMonoidHom = lBar ⊥ V h.hyp151.isElemAbelian L := by
    have h := CFSG.Walter.map_conj_map_conj_inv τ (lBar ⊥ V h.hyp151.isElemAbelian L)
    rw [hmapτ] at h
    rwa [hτinv] at h
  simp only [wTil]
  constructor
  · rw [← s15_Infra_commSub_top_map_conj (lBar ⊥ V h.hyp151.isElemAbelian L) τ, hmapτ]
  · rw [← s15_Infra_commSub_top_map_conj
        (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) τ, hmapτB]

theorem s16h_sl28_centralizer_stabilizes_commSub_fixV
    {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {κ : MulAut W}
    (hκL : κ ∈ Subgroup.centralizer (L : Set (MulAut W))) :
    ∀ z ∈ commSub ⊤ L ⊓ fixV L, κ z ∈ commSub ⊤ L ⊓ fixV L := by
  have hmapL : L.map (MulAut.conj κ).toMonoidHom = L := by
    ext a
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      change MulAut.conj κ b ∈ L
      rw [MulAut.conj_apply]
      have hb' : b * κ = κ * b := Subgroup.mem_centralizer_iff.mp hκL b hb
      rw [← hb', mul_assoc, mul_inv_cancel, mul_one]
      exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      change MulAut.conj κ a = a
      rw [MulAut.conj_apply]
      have ha' : a * κ = κ * a := Subgroup.mem_centralizer_iff.mp hκL a ha
      rw [← ha', mul_assoc, mul_inv_cancel, mul_one]
  have hcomm : (commSub ⊤ L).map κ.toMonoidHom = commSub ⊤ L := by
    have h := s15_Infra_commSub_top_map_conj L κ
    rw [hmapL] at h
    exact h.symm
  intro z hz
  obtain ⟨hzW, hzfix⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hmem : κ z ∈ (commSub ⊤ L).map κ.toMonoidHom := ⟨z, hzW, rfl⟩
    rwa [hcomm] at hmem
  · rw [mem_fixV] at hzfix ⊢
    intro a ha
    have ha' : a * κ = κ * a := Subgroup.mem_centralizer_iff.mp hκL a ha
    calc a (κ z) = (a * κ) z := rfl
      _ = (κ * a) z := by rw [ha']
      _ = κ (a z) := rfl
      _ = κ z := by rw [hzfix a ha]

theorem s16h_sl28_kappa_prime_agrees_on_ZT
    (D : Data G) (S : s16h_Std D)
    {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {τ κ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hκL : κ ∈ Subgroup.centralizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _))
    (hτZ : τ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L),
      (τ * κ * τ⁻¹) z = κ z := by
  have hκZ := s16h_sl28_centralizer_stabilizes_commSub_fixV hκL
  have hτinv : τ⁻¹ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) :=
    (centSub _).inv_mem hτZ
  intro z hz
  have hz' : κ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) := hκZ z hz
  have hτinvz : τ⁻¹ z = z := (mem_centSub.mp hτinv) z hz
  have hτfix : τ (κ z) = κ z := (mem_centSub.mp hτZ) (κ z) hz'
  calc (τ * κ * τ⁻¹) z = τ (κ (τ⁻¹ z)) := rfl
    _ = τ (κ z) := by rw [hτinvz]
    _ = κ z := hτfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
