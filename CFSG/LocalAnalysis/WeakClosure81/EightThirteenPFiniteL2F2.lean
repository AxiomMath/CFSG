module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5S5Cls

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open Equiv
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsL3 IsSp4 IsSL3)
open CFSG.Quasithin.E1.ThinA5 (sA sB pair_conj)

private noncomputable def wc813fl2f2_conjAut {Y : Type} [Group Y] (L : Subgroup Y) (b : Y)
    (hb : b ∈ normalizer (L : Set Y)) : MulAut ↥L :=
  ((MulAut.conj b).subgroupMap L).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hb))

@[simp] private theorem wc813fl2f2_conjAut_apply {Y : Type} [Group Y] (L : Subgroup Y) (b : Y)
    (hb : b ∈ normalizer (L : Set Y)) (l : ↥L) :
    (wc813fl2f2_conjAut L b hb l : Y) = b * (l : Y) * b⁻¹ := by
  simp only [wc813fl2f2_conjAut, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

private noncomputable def wc813fl2f2_conjHom {Y : Type} [Group Y] (L : Subgroup Y) :
    ↥(normalizer (L : Set Y)) →* MulAut ↥L where
  toFun n := wc813fl2f2_conjAut L (n : Y) n.2
  map_one' := by
    ext l
    simp [wc813fl2f2_conjAut_apply]
  map_mul' := by
    intro m n
    ext l
    simp only [wc813fl2f2_conjAut_apply, MulAut.mul_apply]
    change ((m : Y) * (n : Y)) * (l : Y) * ((m : Y) * (n : Y))⁻¹ =
      (m : Y) * ((n : Y) * (l : Y) * (n : Y)⁻¹) * (m : Y)⁻¹
    group

private theorem wc813fl2f2_conjAut_mem_eq {Y : Type} [Group Y] (L : Subgroup Y) {b : Y}
    (hbL : b ∈ L) (hb : b ∈ normalizer (L : Set Y)) :
    wc813fl2f2_conjAut L b hb = MulAut.conj ⟨b, hbL⟩ := by
  ext l
  simp [wc813fl2f2_conjAut_apply, MulAut.conj_apply]

private noncomputable def wc813fl2f2_autPerm :
    MulAut (alternatingGroup (Fin 5)) ≃* Perm (Fin 5) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide))).symm

private theorem wc813fl2f2_autPerm_conjNormal (w : Perm (Fin 5)) :
    wc813fl2f2_autPerm (MulAut.conjNormal (H := alternatingGroup (Fin 5)) w) = w := by
  exact MulEquiv.apply_symm_apply wc813fl2f2_autPerm w

private theorem wc813fl2f2_conjNormal_autPerm (ψ : MulAut (alternatingGroup (Fin 5))) :
    MulAut.conjNormal (H := alternatingGroup (Fin 5)) (wc813fl2f2_autPerm ψ) = ψ := by
  exact MulEquiv.symm_apply_apply wc813fl2f2_autPerm ψ

private noncomputable def wc813fl2f2_permHom {Y : Type} [Group Y] (L : Subgroup Y)
    (e : ↥L ≃* alternatingGroup (Fin 5)) : MulAut ↥L →* Perm (Fin 5) :=
  (wc813fl2f2_autPerm : MulAut (alternatingGroup (Fin 5)) →* Perm (Fin 5)).comp
    (MulAut.congr e : MulAut ↥L →* MulAut (alternatingGroup (Fin 5)))

private theorem wc813fl2f2_congr_conj {X Z : Type} [Group X] [Group Z] (f : X ≃* Z) (x : X) :
    MulAut.congr f (MulAut.conj x) = MulAut.conj (f x) := by
  ext z
  show f ((MulAut.conj x) (f.symm z)) = MulAut.conj (f x) z
  simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem wc813fl2f2_permHom_conjAut_mem {Y : Type} [Group Y] (L : Subgroup Y)
    (e : ↥L ≃* alternatingGroup (Fin 5)) {b : Y} (hbL : b ∈ L)
    (hbN : b ∈ normalizer (L : Set Y)) :
    wc813fl2f2_permHom L e (wc813fl2f2_conjAut L b hbN) = (e ⟨b, hbL⟩ : Perm (Fin 5)) := by
  rw [wc813fl2f2_conjAut_mem_eq L hbL hbN]
  show wc813fl2f2_autPerm (MulAut.congr e (MulAut.conj ⟨b, hbL⟩)) = _
  rw [wc813fl2f2_congr_conj]
  rw [← MulAut.conjNormal_val (h := e ⟨b, hbL⟩)]
  exact wc813fl2f2_autPerm_conjNormal _

private theorem wc813fl2f2_canon :
    ∃ y : ↥(alternatingGroup (Fin 5)),
      (y : Perm (Fin 5)) * sB = sB * (y : Perm (Fin 5)) ∧
      sA * ((y : Perm (Fin 5)) * sA * (y : Perm (Fin 5))⁻¹) ≠
        ((y : Perm (Fin 5)) * sA * (y : Perm (Fin 5))⁻¹) * sA := by
  decide +kernel

private theorem wc813fl2f2_alt5_outer_pair :
    ∀ σ τ : Perm (Fin 5), σ * σ = 1 → τ * τ = 1 → σ * τ = τ * σ →
      Perm.sign σ = -1 → Perm.sign τ = -1 → σ ≠ τ →
      ∃ y : ↥(alternatingGroup (Fin 5)),
        (y : Perm (Fin 5)) * τ = τ * (y : Perm (Fin 5)) ∧
        σ * ((y : Perm (Fin 5)) * σ * (y : Perm (Fin 5))⁻¹) ≠
          ((y : Perm (Fin 5)) * σ * (y : Perm (Fin 5))⁻¹) * σ := by
  intro σ τ hσ2 hτ2 hcomm hσs hτs hne
  obtain ⟨g, hgσ, hgτ⟩ := pair_conj σ τ (by rwa [sq]) (by rwa [sq]) hσs hτs hcomm hne
  obtain ⟨y₀, hy₀comm, hy₀nc⟩ := wc813fl2f2_canon
  have hmem : g⁻¹ * (y₀ : Perm (Fin 5)) * g ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv, Equiv.Perm.mem_alternatingGroup.mp y₀.2, mul_one]
    group
  refine ⟨⟨g⁻¹ * (y₀ : Perm (Fin 5)) * g, hmem⟩, ?_, ?_⟩
  · show g⁻¹ * (y₀ : Perm (Fin 5)) * g * τ = τ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g)
    calc g⁻¹ * (y₀ : Perm (Fin 5)) * g * τ
        = g⁻¹ * (y₀ : Perm (Fin 5)) * (g * τ * g⁻¹) * g := by group
      _ = g⁻¹ * (y₀ : Perm (Fin 5)) * sB * g := by rw [hgτ]
      _ = g⁻¹ * ((y₀ : Perm (Fin 5)) * sB) * g := by group
      _ = g⁻¹ * (sB * (y₀ : Perm (Fin 5))) * g := by rw [hy₀comm]
      _ = g⁻¹ * sB * (y₀ : Perm (Fin 5)) * g := by group
      _ = g⁻¹ * (g * τ * g⁻¹) * (y₀ : Perm (Fin 5)) * g := by rw [hgτ]
      _ = τ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g) := by group
  · show σ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g * σ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g)⁻¹) ≠
      (g⁻¹ * (y₀ : Perm (Fin 5)) * g * σ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g)⁻¹) * σ
    have hσeq : σ = g⁻¹ * sA * g := by rw [← hgσ]; group
    have hkey : σ * (g⁻¹ * (y₀ : Perm (Fin 5)) * g * σ *
          (g⁻¹ * (y₀ : Perm (Fin 5)) * g)⁻¹) =
        g⁻¹ * (sA * ((y₀ : Perm (Fin 5)) * sA * (y₀ : Perm (Fin 5))⁻¹)) * g := by
      rw [hσeq]
      group
    have hkey2 : (g⁻¹ * (y₀ : Perm (Fin 5)) * g * σ *
          (g⁻¹ * (y₀ : Perm (Fin 5)) * g)⁻¹) * σ =
        g⁻¹ * (((y₀ : Perm (Fin 5)) * sA * (y₀ : Perm (Fin 5))⁻¹) * sA) * g := by
      rw [hσeq]
      group
    rw [hkey, hkey2]
    intro hcon
    apply hy₀nc
    have := congrArg (fun q : Perm (Fin 5) => g * q * g⁻¹) hcon
    simpa [mul_assoc] using this

private theorem wc813fl2f2_units_one_ne_neg_one : (1 : ℤˣ) ≠ -1 := by
  intro h
  have hz : (1 : ℤ) = -1 := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at hz

theorem wc813fl2_fourGroupInnerOn_L2 : FourGroupInnerOn ShapeL2 := by
  intro Y _ _ L A hL hA hAe hA4 hAC hK1
  classical
  obtain ⟨-, hL2⟩ := hL
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L
    (show CFSG.Blueprint.LieModel ↥L .PSL 2 2 2 from hL2)
  let ρ : ↥A →* MulAut ↥L :=
    (wc813fl2f2_conjHom L).comp (Subgroup.inclusion hA)
  let ζ : ↥A →* Perm (Fin 5) := (wc813fl2f2_permHom L e).comp ρ
  have hρapply : ∀ (a : ↥A) (l : ↥L), ((ρ a) l : Y) = (a : Y) * (l : Y) * (a : Y)⁻¹ := by
    intro a l
    change (wc813fl2f2_conjAut L (a : Y) (hA a.2) l : Y) = (a : Y) * (l : Y) * (a : Y)⁻¹
    exact wc813fl2f2_conjAut_apply L (a : Y) (hA a.2) l
  have hζconjNormal : ∀ a : ↥A,
      MulAut.conjNormal (H := alternatingGroup (Fin 5)) (ζ a) = MulAut.congr e (ρ a) := by
    intro a
    change MulAut.conjNormal (H := alternatingGroup (Fin 5))
      (wc813fl2f2_autPerm (MulAut.congr e (ρ a))) = MulAut.congr e (ρ a)
    exact wc813fl2f2_conjNormal_autPerm _
  have hρker : ρ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hpa : ρ a = 1 := MonoidHom.mem_ker.mp ha
    have hmem : (a : Y) ∈ A ⊓ centralizer (L : Set Y) := by
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h3 : (a : Y) * l * (a : Y)⁻¹ = l := by
        have h2 := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hpa
        simp only [MulAut.one_apply] at h2
        have h4 := congrArg Subtype.val h2
        rw [hρapply a ⟨l, hl⟩] at h4
        simpa using h4
      calc l * (a : Y) = ((a : Y) * l * (a : Y)⁻¹) * (a : Y) := by rw [h3]
        _ = (a : Y) * l := by group
    have ha1 : (a : Y) = 1 := by
      have h := hmem
      rw [hAC] at h
      simpa using h
    exact Subtype.ext ha1
  have hζker : ζ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hconj : MulAut.conjNormal (H := alternatingGroup (Fin 5)) (ζ a) = 1 := by
      have hza : ζ a = 1 := MonoidHom.mem_ker.mp ha
      rw [hza, map_one]
    rw [hζconjNormal a] at hconj
    have hpa : ρ a = 1 := (MulAut.congr e).injective (by rw [map_one]; exact hconj)
    have hmemker : a ∈ ρ.ker := hpa
    rw [hρker] at hmemker
    simpa using hmemker
  have hζinj : Function.Injective ζ := (MonoidHom.ker_eq_bot_iff ζ).mp hζker
  have hmain : ∀ a : ↥A, ζ a ∈ alternatingGroup (Fin 5) := by
    intro aA
    by_contra hodd
    set σ : Perm (Fin 5) := ζ aA with hσdef
    have hσsign : Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hodd
      · exact h
    have haA2 : aA * aA = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hAe.2 (aA : Y) aA.2
    have hσ2 : σ * σ = 1 := by
      have h1 : ζ (aA * aA) = ζ aA * ζ aA := map_mul ζ aA aA
      rw [haA2, map_one] at h1
      rw [hσdef]
      exact h1.symm
    haveI : Fintype ↥A := Fintype.ofFinite ↥A
    have hcardA : Fintype.card ↥A = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hA4
    have hcompl : Fintype.card {x : ↥A // x ≠ 1} = 3 := by
      have h := Fintype.card_subtype_compl (p := fun x : ↥A => x = 1)
      rw [Fintype.card_subtype_eq (1 : ↥A), hcardA] at h
      omega
    have haA_ne_one : aA ≠ 1 := by
      intro h
      apply hodd
      rw [hσdef, h, map_one]
      exact one_mem _
    obtain ⟨b, hb_ne⟩ := Fintype.exists_ne_of_one_lt_card
      (show 1 < Fintype.card {x : ↥A // x ≠ 1} by rw [hcompl]; norm_num)
      (⟨aA, haA_ne_one⟩ : {x : ↥A // x ≠ 1})
    have hbA_ne_one : b.1 ≠ 1 := b.2
    have hbA_ne_aA : b.1 ≠ aA := by
      intro h
      exact hb_ne (Subtype.ext h)
    set βA : ↥A := if Perm.sign (ζ b.1) = -1 then b.1 else aA * b.1 with hβdef
    have hβsign : Perm.sign (ζ βA) = -1 := by
      rw [hβdef]
      by_cases h : Perm.sign (ζ b.1) = -1
      · simp only [h, if_true]
      · simp only [h, if_false]
        have hb1s : Perm.sign (ζ b.1) = 1 := by
          rcases Int.units_eq_one_or (Perm.sign (ζ b.1)) with h' | h'
          · exact h'
          · exact absurd h' h
        rw [map_mul, ← hσdef, map_mul, hσsign, hb1s]
        simp
    have hβA2 : βA * βA = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hAe.2 (βA : Y) βA.2
    have hτ2 : ζ βA * ζ βA = 1 := by
      have h1 : ζ (βA * βA) = ζ βA * ζ βA := map_mul ζ βA βA
      rw [hβA2, map_one] at h1
      exact h1.symm
    have hβ_ne_aA : βA ≠ aA := by
      rw [hβdef]
      by_cases h : Perm.sign (ζ b.1) = -1
      · simp only [h, if_true]
        exact hbA_ne_aA
      · simp only [h, if_false]
        intro heq
        have h2 := congrArg (fun x : ↥A => aA⁻¹ * x) heq
        simp only [mul_one, ← mul_assoc, inv_mul_cancel, one_mul] at h2
        exact hbA_ne_one h2
    have hτne : ζ βA ≠ σ := by
      intro h
      exact hβ_ne_aA (hζinj (h.trans hσdef))
    have hβY_ne_one : (βA : Y) ≠ 1 := by
      intro hY
      have hβ1 : βA = 1 := Subtype.ext hY
      have hζ1 : ζ βA = 1 := by rw [hβ1, map_one]
      have hsign1 := hβsign
      rw [hζ1, map_one] at hsign1
      exact wc813fl2f2_units_one_ne_neg_one hsign1
    have hσβcomm : σ * ζ βA = ζ βA * σ := by
      have hcommA : aA * βA = βA * aA := hAe.1.is_comm.comm aA βA
      calc σ * ζ βA = ζ aA * ζ βA := by rw [hσdef]
        _ = ζ (aA * βA) := (map_mul ζ aA βA).symm
        _ = ζ (βA * aA) := by rw [hcommA]
        _ = ζ βA * ζ aA := map_mul ζ βA aA
        _ = ζ βA * σ := by rw [hσdef]
    obtain ⟨y, hycomm, hyne⟩ := wc813fl2f2_alt5_outer_pair σ (ζ βA)
      hσ2 hτ2 hσβcomm hσsign hβsign hτne.symm
    let xL : ↥L := e.symm y
    have hxey : e xL = y := by simp [xL]
    have hxN : (xL : Y) ∈ normalizer (L : Set Y) := Subgroup.le_normalizer xL.2
    have hxLfix : ρ βA xL = xL := by
      apply e.injective
      apply Subtype.ext
      have h1 : (e (ρ βA xL) : Perm (Fin 5)) =
          ((MulAut.conjNormal (H := alternatingGroup (Fin 5)) (ζ βA)) (e xL) :
            Perm (Fin 5)) := by
        have h := congrArg (fun f : MulAut (alternatingGroup (Fin 5)) => f (e xL))
          (hζconjNormal βA)
        have h2 : (MulAut.congr e (ρ βA)) (e xL) = e (ρ βA xL) := by
          simp [MulAut.congr]
        rw [h2] at h
        exact congrArg (fun z : ↥(alternatingGroup (Fin 5)) => (z : Perm (Fin 5))) h.symm
      rw [h1, MulAut.conjNormal_apply, hxey]
      show (ζ βA) * (y : Perm (Fin 5)) * (ζ βA)⁻¹ = (y : Perm (Fin 5))
      rw [← hycomm]
      group
    have hxβ : (xL : Y) * (βA : Y) = (βA : Y) * (xL : Y) := by
      have h := congrArg Subtype.val hxLfix
      rw [hρapply βA xL] at h
      calc (xL : Y) * (βA : Y) = ((βA : Y) * (xL : Y) * (βA : Y)⁻¹) * (βA : Y) := by
            rw [h]
        _ = (βA : Y) * (xL : Y) := by group
    have hxcent : (xL : Y) ∈ centralizer ({(βA : Y)} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxβ
    let H : Subgroup Y := Subgroup.closure
      {γ : Y | ∃ x ∈ L ⊓ centralizer ({(βA : Y)} : Set Y), γ = x * (aA : Y) * x⁻¹}
    have hHab : IsElemAbelian 2 H := hK1 (aA : Y) aA.2 (βA : Y) βA.2 hβY_ne_one
    have hone_mem : (1 : Y) ∈ L ⊓ centralizer ({(βA : Y)} : Set Y) :=
      Subgroup.mem_inf.mpr ⟨one_mem L, one_mem _⟩
    have hx_mem : (xL : Y) ∈ L ⊓ centralizer ({(βA : Y)} : Set Y) :=
      Subgroup.mem_inf.mpr ⟨xL.2, hxcent⟩
    let u0 : ↥H := ⟨(aA : Y), Subgroup.subset_closure ⟨1, hone_mem, by group⟩⟩
    let u1 : ↥H := ⟨(xL : Y) * (aA : Y) * (xL : Y)⁻¹,
      Subgroup.subset_closure ⟨(xL : Y), hx_mem, rfl⟩⟩
    have hcommH : u0 * u1 = u1 * u0 := hHab.1.is_comm.comm u0 u1
    have hcommY : (u0 : Y) * (u1 : Y) = (u1 : Y) * (u0 : Y) := by
      have h := congrArg Subtype.val hcommH
      simpa using h
    have h0N : (u0 : Y) ∈ normalizer (L : Set Y) := hA aA.2
    have h1N : (u1 : Y) ∈ normalizer (L : Set Y) :=
      mul_mem (mul_mem hxN (hA aA.2)) (inv_mem hxN)
    have hconjcomm :
        wc813fl2f2_conjAut L (u0 : Y) h0N * wc813fl2f2_conjAut L (u1 : Y) h1N =
        wc813fl2f2_conjAut L (u1 : Y) h1N * wc813fl2f2_conjAut L (u0 : Y) h0N := by
      ext l
      simp only [MulAut.mul_apply, wc813fl2f2_conjAut_apply]
      have hcommYinv : (u1 : Y)⁻¹ * (u0 : Y)⁻¹ = (u0 : Y)⁻¹ * (u1 : Y)⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcommY]
      calc (u0 : Y) * ((u1 : Y) * (l : Y) * (u1 : Y)⁻¹) * (u0 : Y)⁻¹
          = ((u0 : Y) * (u1 : Y)) * (l : Y) * ((u1 : Y)⁻¹ * (u0 : Y)⁻¹) := by group
        _ = ((u1 : Y) * (u0 : Y)) * (l : Y) * ((u1 : Y)⁻¹ * (u0 : Y)⁻¹) := by rw [hcommY]
        _ = ((u1 : Y) * (u0 : Y)) * (l : Y) * ((u0 : Y)⁻¹ * (u1 : Y)⁻¹) := by rw [hcommYinv]
        _ = (u1 : Y) * ((u0 : Y) * (l : Y) * (u0 : Y)⁻¹) * (u1 : Y)⁻¹ := by group
    have hχu0 : wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u0 : Y) h0N) = σ := by
      change ζ aA = σ
      rw [hσdef]
    have hχu1 : wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u1 : Y) h1N) =
        (y : Perm (Fin 5)) * σ * (y : Perm (Fin 5))⁻¹ := by
      have hu1decomp : wc813fl2f2_conjAut L (u1 : Y) h1N =
          wc813fl2f2_conjAut L (xL : Y) hxN *
            wc813fl2f2_conjAut L (aA : Y) (hA aA.2) *
            (wc813fl2f2_conjAut L (xL : Y) hxN)⁻¹ := by
        change (wc813fl2f2_conjHom L)
            (⟨(xL : Y), hxN⟩ * ⟨(aA : Y), hA aA.2⟩ * ⟨(xL : Y), hxN⟩⁻¹) =
          (wc813fl2f2_conjHom L) ⟨(xL : Y), hxN⟩ *
            (wc813fl2f2_conjHom L) ⟨(aA : Y), hA aA.2⟩ *
            ((wc813fl2f2_conjHom L) ⟨(xL : Y), hxN⟩)⁻¹
        simp only [map_mul, map_inv]
      have hxLχ : wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (xL : Y) hxN) =
          (y : Perm (Fin 5)) := by
        rw [wc813fl2f2_permHom_conjAut_mem L e xL.2 hxN]
        exact congrArg (fun z : ↥(alternatingGroup (Fin 5)) => (z : Perm (Fin 5))) hxey
      have haχ : wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (aA : Y) (hA aA.2)) = σ := by
        change ζ aA = σ
        rw [hσdef]
      rw [hu1decomp, map_mul, map_mul, map_inv, hxLχ, haχ]
    have hpermcomm : wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u0 : Y) h0N) *
        wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u1 : Y) h1N) =
        wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u1 : Y) h1N) *
        wc813fl2f2_permHom L e (wc813fl2f2_conjAut L (u0 : Y) h0N) := by
      simpa only [map_mul] using congrArg (wc813fl2f2_permHom L e) hconjcomm
    rw [hχu0, hχu1] at hpermcomm
    exact hyne hpermcomm
  intro a ha
  have hζA : ζ ⟨a, ha⟩ ∈ alternatingGroup (Fin 5) := hmain ⟨a, ha⟩
  let s : ↥L := e.symm ⟨ζ ⟨a, ha⟩, hζA⟩
  have hes : e s = ⟨ζ ⟨a, ha⟩, hζA⟩ := by simp [s]
  have hρeq : ρ ⟨a, ha⟩ = MulAut.conj s := by
    apply (MulAut.congr e).injective
    have h1 : MulAut.congr e (ρ ⟨a, ha⟩) =
        MulAut.conjNormal (H := alternatingGroup (Fin 5)) (ζ ⟨a, ha⟩) :=
      (hζconjNormal ⟨a, ha⟩).symm
    have h2 : MulAut.congr e (MulAut.conj s) =
        MulAut.conjNormal (H := alternatingGroup (Fin 5)) (ζ ⟨a, ha⟩) := by
      rw [wc813fl2f2_congr_conj, hes]
      rw [← MulAut.conjNormal_val
        (h := (⟨ζ ⟨a, ha⟩, hζA⟩ : ↥(alternatingGroup (Fin 5))))]
    rw [h1, h2]
  have hcomm : (s : Y)⁻¹ * a ∈ centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hcongr := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hρeq
    have h3 : (a : Y) * l * (a : Y)⁻¹ = (s : Y) * l * (s : Y)⁻¹ := by
      have h1 : (((ρ ⟨a, ha⟩) ⟨l, hl⟩ : ↥L) : Y) = (a : Y) * l * (a : Y)⁻¹ :=
        hρapply ⟨a, ha⟩ ⟨l, hl⟩
      have h2 : (((MulAut.conj s) ⟨l, hl⟩ : ↥L) : Y) = (s : Y) * l * (s : Y)⁻¹ := by
        rw [MulAut.conj_apply]
        rfl
      have h4 := congrArg (fun z : ↥L => (z : Y)) hcongr
      rw [h1, h2] at h4
      exact h4
    have h4 : ((s : Y)⁻¹ * a) * l = l * ((s : Y)⁻¹ * a) := by
      calc ((s : Y)⁻¹ * a) * l
          = (s : Y)⁻¹ * (a * l * a⁻¹) * a := by group
        _ = (s : Y)⁻¹ * ((s : Y) * l * (s : Y)⁻¹) * a := by rw [h3]
        _ = l * ((s : Y)⁻¹ * a) := by group
    exact h4.symm
  have hmem : (s : Y) * ((s : Y)⁻¹ * a) ∈ L ⊔ centralizer (L : Set Y) :=
    Subgroup.mul_mem_sup s.2 hcomm
  rwa [show (s : Y) * ((s : Y)⁻¹ * a) = a by group] at hmem

end CFSG.LocalAnalysis.WeakClosure81

end
