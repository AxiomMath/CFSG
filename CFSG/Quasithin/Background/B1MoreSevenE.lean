module

public import CFSG.Quasithin.Background.B1MoreSevenC
public import CFSG.Quasithin.Background.B1MoreSevenD

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V]

namespace B72Hyp

variable {H A : Subgroup (MulAut V)} {a : MulAut V} {I : Subgroup V}

theorem irr_map (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) :
    I.map b.toMonoidHom ∈ IrrPlus H (⊤ : Subgroup V) :=
  irrPlus_map (fun x hx => P.conj_mem hb hx)
    (fun x hx => by simpa using P.conj_mem (A.inv_mem hb) hx) P.hI

def Jb (H : Subgroup (MulAut V)) (I : Subgroup V) (b : MulAut V) : Subgroup V :=
  I.map b.toMonoidHom ⊔ fixV H

theorem Jb_inf (P : B72Hyp H A a I) {c c' : MulAut V} (hc : c ∈ A) (hc' : c' ∈ A)
    (hne : I.map c.toMonoidHom ≠ I.map c'.toMonoidHom) : Jb H I c ⊓ Jb H I c' = fixV H := by
  rcases irrPlus_sup_inf (P.irr_map hc) (P.irr_map hc') with h | h
  · exact absurd h hne
  · exact h

theorem map_eq_of_Jb_eq (P : B72Hyp H A a I) {c c' : MulAut V} (hc : c ∈ A) (hc' : c' ∈ A)
    (h : Jb H I c = Jb H I c') : I.map c.toMonoidHom = I.map c'.toMonoidHom := by
  by_contra hne
  have h1 := P.Jb_inf hc hc' hne
  rw [← h, inf_idem] at h1
  have h2 : I.map c.toMonoidHom ≤ fixV H := le_sup_left.trans h1.le
  apply P.not_le
  intro i hi
  have h3 : c i ∈ fixV H := h2 ⟨i, hi, rfl⟩
  have := P.fixV_inv (A.inv_mem hc) h3
  simpa using this

theorem card_Jb [Finite V] (P : B72Hyp H A a I) {b : MulAut V} (hb : b ∈ A) :
    Nat.card ↥(Jb H I b) = Nat.card ↥(I ⊔ fixV H) := by
  have h : Jb H I b = (I ⊔ fixV H).map b.toMonoidHom := by
    rw [Subgroup.map_sup, P.map_fixV hb]
    rfl
  rw [h]
  exact Subgroup.card_map_of_injective b.injective

theorem inv_mul_mem_centSub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B72Hyp H A a I)
    (hH : oTwoUpper H = H) (hCF : AllTwoChiefFactorsCentral H) {c c' : MulAut V} (hc : c ∈ A)
    (hc' : c' ∈ A) (h : I.map c.toMonoidHom = I.map c'.toMonoidHom) :
    c⁻¹ * c' ∈ centSub (I ⊔ I.map a.toMonoidHom) := by
  have hd : c⁻¹ * c' ∈ A := A.mul_mem (A.inv_mem hc) hc'
  have hdI : ∀ x, (c⁻¹ * c') x ∈ I ↔ x ∈ I := by
    intro x
    have e1 : c ((c⁻¹ * c') x) = c' x := by simp [MulAut.mul_apply]
    constructor
    · intro hx
      have h1 : c' x ∈ I.map c'.toMonoidHom := by
        rw [← h]
        exact ⟨_, hx, e1⟩
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := c'.injective hyx
      rw [← this]; exact hy
    · intro hx
      have h1 : c' x ∈ I.map c.toMonoidHom := by
        rw [h]; exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = (c⁻¹ * c') x := by
        apply c.injective
        rw [e1]; exact hyx
      rw [← this]; exact hy
  exact P.fixes_of_trivial_mod hV hH hCF hd (P.stab_trivial_mod hd hdI)

theorem Dp_inf_Ip (P : B72Hyp H A a I) :
    (Dsub a I ⊔ fixV H) ⊓ (I ⊔ fixV H) = fixV H := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro v ⟨hvD, hvI⟩
  obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hvD
  obtain ⟨i, hi, rfl⟩ := mem_Dsub.1 hd
  have h1 : a i ∈ I ⊔ fixV H := by
    have e : a i = ((a i * i⁻¹) * z) * z⁻¹ * i := by group
    rw [e]
    exact (I ⊔ fixV H).mul_mem ((I ⊔ fixV H).mul_mem hvI
      ((I ⊔ fixV H).inv_mem (Subgroup.mem_sup_right hz))) (Subgroup.mem_sup_left hi)
  have h2 : a i ∈ I.map a.toMonoidHom ⊔ fixV H := Subgroup.mem_sup_left ⟨i, hi, rfl⟩
  have h3 : a i ∈ fixV H := by
    have : a i ∈ (I ⊔ fixV H) ⊓ (I.map a.toMonoidHom ⊔ fixV H) := ⟨h1, h2⟩
    rwa [P.disj] at this
  have h4 : i ∈ fixV H := by
    have := P.fixV_inv (A.inv_mem P.ha) h3
    simpa using this
  exact (fixV H).mul_mem ((fixV H).mul_mem h3 ((fixV H).inv_mem h4)) hz

theorem Dp_sup_Ip (H : Subgroup (MulAut V)) (a : MulAut V) (I : Subgroup V) :
    (Dsub a I ⊔ fixV H) ⊔ (I ⊔ fixV H) = (I ⊔ I.map a.toMonoidHom) ⊔ fixV H := by
  refine le_antisymm
    (sup_le (sup_le ((Dsub_le_W a I).trans le_sup_left) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
  refine sup_le (sup_le (le_sup_of_le_right le_sup_left) ?_)
    (le_sup_of_le_left le_sup_right)
  rintro _ ⟨i, hi, rfl⟩
  have h1 : a i * i⁻¹ ∈ (Dsub a I ⊔ fixV H) ⊔ (I ⊔ fixV H) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_Dsub.2 ⟨i, hi, rfl⟩))
  have h2 : i ∈ (Dsub a I ⊔ fixV H) ⊔ (I ⊔ fixV H) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left hi)
  have := Subgroup.mul_mem _ h1 h2
  simpa using this

theorem Ip_sup_I'p (H : Subgroup (MulAut V)) (a : MulAut V) (I : Subgroup V) :
    (I ⊔ fixV H) ⊔ (I.map a.toMonoidHom ⊔ fixV H) = (I ⊔ I.map a.toMonoidHom) ⊔ fixV H := by
  refine le_antisymm (sup_le (sup_le_sup_right le_sup_left _) (sup_le_sup_right le_sup_right _)) ?_
  exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left))
    (le_sup_of_le_left le_sup_right)

theorem card_Wp_mul [Finite V] (P : B72Hyp H A a I) :
    Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊔ fixV H) * Nat.card ↥(fixV H) =
      Nat.card ↥(I ⊔ fixV H) * Nat.card ↥(I ⊔ fixV H) := by
  have h2 := card_sup_mul_card_inf (I ⊔ fixV H) (I.map a.toMonoidHom ⊔ fixV H)
  have h3 : Nat.card ↥(I.map a.toMonoidHom ⊔ fixV H) = Nat.card ↥(I ⊔ fixV H) :=
    P.card_Jb P.ha
  rw [Ip_sup_I'p H a I, P.disj, h3] at h2
  exact h2

theorem card_Dp [Finite V] (P : B72Hyp H A a I) :
    Nat.card ↥(Dsub a I ⊔ fixV H) = Nat.card ↥(I ⊔ fixV H) := by
  have h1 := card_sup_mul_card_inf (Dsub a I ⊔ fixV H) (I ⊔ fixV H)
  rw [Dp_sup_Ip H a I, P.Dp_inf_Ip] at h1
  have hpos : 0 < Nat.card ↥(I ⊔ fixV H) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans P.card_Wp_mul)

theorem Dp_inf_Jb (P : B72Hyp H A a I) {c : MulAut V} (hc : c ∈ A) :
    (Dsub a I ⊔ fixV H) ⊓ Jb H I c = fixV H := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro v ⟨hvD, hvJ⟩
  obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.1 hvD
  have hav : a (d * z) * (d * z)⁻¹ ∈ fixV H := by
    rw [map_mul, P.Dsub_fixed P.ha hd]
    have e : d * a z * (d * z)⁻¹ = a z * z⁻¹ := by cgroup
    rw [e]
    exact (fixV H).mul_mem (P.fixV_inv P.ha hz) ((fixV H).inv_mem hz)
  obtain ⟨y, hy, z₀, hz₀, hyv⟩ := Subgroup.mem_sup.1 hvJ
  obtain ⟨i, hi, hiy⟩ := hy
  have hiy' : c i = y := hiy
  subst hiy'
  have hJ1 : a (d * z) ∈ Jb H I (a * c) := by
    rw [← hyv, map_mul]
    exact Subgroup.mul_mem_sup ⟨i, hi, rfl⟩ (P.fixV_inv P.ha hz₀)
  have hJ2 : d * z ∈ Jb H I (a * c) := by
    have e : d * z = a (d * z) * (a (d * z) * (d * z)⁻¹)⁻¹ := by cgroup
    rw [e]
    exact Subgroup.mul_mem _ hJ1 (Subgroup.inv_mem _ (Subgroup.mem_sup_right hav))
  have hne : I.map c.toMonoidHom ≠ I.map (a * c).toMonoidHom := by
    intro h
    apply P.hne
    have hac : a * c = c * a := P.abel a P.ha c hc
    have hcomm : ∀ x, a (c x) = c (a x) := fun x => by
      simpa [MulAut.mul_apply] using congrArg (fun φ : MulAut V => φ x) hac
    ext x
    constructor
    · rintro ⟨i', hi', rfl⟩
      have h1 : (a * c) i' ∈ I.map c.toMonoidHom := by rw [h]; exact ⟨i', hi', rfl⟩
      obtain ⟨y, hy, hyc⟩ := h1
      have e1 : c y = (a * c) i' := hyc
      have hyc' : c y = c (a i') := by
        rw [e1, MulAut.mul_apply]; exact hcomm i'
      have hyy : y = a i' := c.injective hyc'
      have hyi : a i' ∈ I := hyy ▸ hy
      exact hyi
    · intro hx
      have h1 : c x ∈ I.map (a * c).toMonoidHom := by rw [← h]; exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyc⟩ := h1
      refine ⟨y, hy, ?_⟩
      have e1 : a (c y) = c x := hyc
      have e2 : c (a y) = c x := by rw [← hcomm]; exact e1
      show a y = x
      exact c.injective e2
  have h3 : d * z ∈ Jb H I c ⊓ Jb H I (a * c) := ⟨hvJ, hJ2⟩
  rwa [P.Jb_inf hc (A.mul_mem P.ha hc) hne] at h3

theorem card_offender [Finite V] {G : Subgroup (MulAut V)} (hOff : IsFFStarOffender G A)
    (W : Subgroup V) :
    Nat.card ↥W * Nat.card ↥(A ⊓ centSub W) ≤ Nat.card ↥A * Nat.card ↥(W ⊓ fixV A) := by
  have h := B1.card_inf_fixV_le hOff (inf_le_left : A ⊓ centSub W ≤ A) W
  rw [inf_eq_left.2 (B1.fixV_inf_centSub (A := A) W)] at h
  rw [mul_comm]
  exact h

theorem card_D_mul_le [Finite V] (P : B72Hyp H A a I) :
    Nat.card ↥(Dsub a I) * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) ≤
      Nat.card ↥(I ⊔ I.map a.toMonoidHom) := by
  have h1 := B1More.card_map_mul_card_inf_ker (I ⊔ I.map a.toMonoidHom) (psiHom a)
  have h2 : Nat.card ↥(Dsub a I) ≤ Nat.card ↥((I ⊔ I.map a.toMonoidHom).map (psiHom a)) :=
    Subgroup.card_le_of_le (Subgroup.map_mono le_sup_left)
  have h3 : Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) ≤
      Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ (psiHom a).ker) := by
    refine Subgroup.card_le_of_le (inf_le_inf_left _ ?_)
    intro v hv
    rw [MonoidHom.mem_ker, psiHom_apply, mul_inv_eq_one]
    exact hv a P.ha
  calc _ ≤ Nat.card ↥((I ⊔ I.map a.toMonoidHom).map (psiHom a)) *
        Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ (psiHom a).ker) := Nat.mul_le_mul h2 h3
    _ = _ := h1

theorem false_of_B72 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (hOff : IsFFStarOffender G A) (P : B72Hyp H A a I) (hH : oTwoUpper H = H)
    (hCF : AllTwoChiefFactorsCentral H) : False := by
  obtain ⟨invI, -, -, -⟩ := mem_irrPlus_top_iff.1 P.hI
  obtain ⟨invI', -, -, -⟩ := mem_irrPlus_top_iff.1 P.irr'
  obtain ⟨s, hs1, hs2, hs3⟩ := card_le_card_image_mul A (A ⊓ centSub (I ⊔ I.map a.toMonoidHom))
    (fun b => Jb H I b) (fun b hb b' hb' h =>
      ⟨A.mul_mem (A.inv_mem hb) hb',
        P.inv_mul_mem_centSub hV hH hCF hb hb' (P.map_eq_of_Jb_eq hb hb' h)⟩)
  have hJZ : ∀ J ∈ s, fixV H ≤ J := by
    intro J hJ
    obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    exact le_sup_right
  have hWinv : ∀ b ∈ A, I.map b.toMonoidHom ≤ I ⊔ I.map a.toMonoidHom := by
    rintro b hb _ ⟨i, hi, rfl⟩
    exact P.W_inv_A b hb i (Subgroup.mem_sup_left hi)
  have hJW : ∀ J ∈ s, J ≤ (I ⊔ I.map a.toMonoidHom) ⊔ fixV H := by
    intro J hJ
    obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    exact sup_le_sup_right (hWinv b hb) _
  have hDW : Dsub a I ⊔ fixV H ≤ (I ⊔ I.map a.toMonoidHom) ⊔ fixV H :=
    sup_le_sup_right (Dsub_le_W a I) _
  have hJJ : ∀ J ∈ s, ∀ J' ∈ s, J ≠ J' → J ⊓ J' = fixV H := by
    intro J hJ J' hJ' hne
    obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    obtain ⟨b', hb', rfl⟩ := hs2 J' hJ'
    refine P.Jb_inf hb hb' fun h => hne ?_
    unfold Jb
    rw [h]
  have hDJ : ∀ J ∈ s, (Dsub a I ⊔ fixV H) ⊓ J = fixV H := by
    intro J hJ
    obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    exact P.Dp_inf_Jb hb
  have hJcard : ∀ J ∈ s, Nat.card ↥J = Nat.card ↥(I ⊔ fixV H) := by
    intro J hJ
    obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    exact P.card_Jb hb
  have hQ : Nat.card ↥(I ⊔ fixV H) ≤ s.card * Nat.card ↥(fixV H) := by
    have hc : 0 < Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) := Nat.card_pos
    have he : 0 < Nat.card ↥(A ⊓ centSub (I ⊔ I.map a.toMonoidHom)) := Nat.card_pos
    have h5 := card_offender hOff (I ⊔ I.map a.toMonoidHom)
    have h7 : Nat.card ↥(I ⊔ I.map a.toMonoidHom) ≤
        s.card * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) := by
      have : Nat.card ↥(I ⊔ I.map a.toMonoidHom) *
          Nat.card ↥(A ⊓ centSub (I ⊔ I.map a.toMonoidHom)) ≤
          (s.card * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A)) *
            Nat.card ↥(A ⊓ centSub (I ⊔ I.map a.toMonoidHom)) := by
        calc _ ≤ Nat.card ↥A * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) := h5
          _ ≤ (s.card * Nat.card ↥(A ⊓ centSub (I ⊔ I.map a.toMonoidHom))) *
              Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) := Nat.mul_le_mul_right _ hs3
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_right this he
    have h9 : Nat.card ↥(Dsub a I) ≤ s.card := by
      have : Nat.card ↥(Dsub a I) * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) ≤
          s.card * Nat.card ↥((I ⊔ I.map a.toMonoidHom) ⊓ fixV A) :=
        P.card_D_mul_le.trans h7
      exact Nat.le_of_mul_le_mul_right this hc
    have h10 : Nat.card ↥(Dsub a I ⊔ fixV H) ≤ Nat.card ↥(Dsub a I) * Nat.card ↥(fixV H) := by
      have := card_sup_mul_card_inf (Dsub a I) (fixV H)
      have hpos : 0 < Nat.card ↥(Dsub a I ⊓ fixV H) := Nat.card_pos
      calc Nat.card ↥(Dsub a I ⊔ fixV H)
          ≤ Nat.card ↥(Dsub a I ⊔ fixV H) * Nat.card ↥(Dsub a I ⊓ fixV H) :=
            Nat.le_mul_of_pos_right _ hpos
        _ = _ := this
    calc Nat.card ↥(I ⊔ fixV H) = Nat.card ↥(Dsub a I ⊔ fixV H) := P.card_Dp.symm
      _ ≤ Nat.card ↥(Dsub a I) * Nat.card ↥(fixV H) := h10
      _ ≤ s.card * Nat.card ↥(fixV H) := Nat.mul_le_mul_right _ h9
  have hcov := cover_of_card (fixV H) ((I ⊔ I.map a.toMonoidHom) ⊔ fixV H) (Dsub a I ⊔ fixV H) s
    le_sup_right hJZ hJW le_sup_right hDW hJJ hDJ _ hJcard P.card_Dp P.card_Wp_mul hQ
  apply P.not_invariant_DZ
  intro h hh y hy
  have hWp_inv : ∀ g ∈ H, ∀ x ∈ (I ⊔ I.map a.toMonoidHom) ⊔ fixV H, g x ∈
      (I ⊔ I.map a.toMonoidHom) ⊔ fixV H :=
    isInv_sup (isInv_sup invI invI') (isInv_fixV H)
  have hhy : h y ∈ (I ⊔ I.map a.toMonoidHom) ⊔ fixV H := hWp_inv h hh y (hDW hy)
  rcases hcov _ hhy with h1 | ⟨J, hJ, h1⟩
  · exact h1
  · obtain ⟨b, hb, rfl⟩ := hs2 J hJ
    obtain ⟨invIb, -, -, -⟩ := mem_irrPlus_top_iff.1 (P.irr_map hb)
    have hJinv : ∀ g ∈ H, ∀ x ∈ Jb H I b, g x ∈ Jb H I b :=
      isInv_sup invIb (isInv_fixV H)
    have hy' : y ∈ Jb H I b := by
      have := hJinv h⁻¹ (H.inv_mem hh) _ h1
      simpa using this
    have hyZ : y ∈ fixV H := by
      have : y ∈ (Dsub a I ⊔ fixV H) ⊓ Jb H I b := ⟨hy, hy'⟩
      rwa [P.Dp_inf_Jb hb] at this
    have : h y = y := hyZ h hh
    rw [this]
    exact hy

end B72Hyp

end CFSG.Quasithin
