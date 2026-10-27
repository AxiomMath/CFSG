module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5A
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5B
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C23
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C22

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_q2_le_normalizer_conjugate_x
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    Q2 L1 L2 S ≤ Subgroup.normalizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) := by
  intro q hq
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hq' : d.w * q * d.w⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P2 L1 L2 S) (hL2P d.hwH2)) q).mp hq
  have hq'P : d.w * q * d.w⁻¹ ∈ P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) ((le_sup_right : S ≤ bigB L1 L2 S)
      (str83G4_q2_le_s hfr hq'))
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  rw [CFSG.mem_conjugate_iff, CFSG.mem_conjugate_iff,
    show d.w * (q * x * q⁻¹) * d.w⁻¹ =
      (d.w * q * d.w⁻¹) * (d.w * x * d.w⁻¹) * (d.w * q * d.w⁻¹)⁻¹ by group]
  exact Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hq'P) _

theorem str83G4_y_le_q2
    (hfr : Str83G4Frame L1 L2 S a) : str83Y L1 L2 S ≤ Q2 L1 L2 S := fun y hy =>
  (Subgroup.mem_inf.mp (str83G4_centralizer_x_le hfr (str83G4_not_le_normalizer_z2 hfr)
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (str83G4_q1_le_s hfr (Subgroup.mem_inf.mp hy).1),
      (Subgroup.mem_inf.mp hy).2⟩))).2

theorem str83G4_q2_le_normalizer_y_inf_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    Q2 L1 L2 S ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) :
        Set G) := by
  intro q hq
  have hqP : q ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr hq))
  exact A4.mem_normalizer_inf (A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hqP)
    (F7.normalizer_le_normalizer_centralizer _ (le_normalizer_str83X L1 L2 S hqP)))
    (F7.normalizer_le_normalizer_centralizer _ (str83G4_q2_le_normalizer_conjugate_x hfr d hq))

theorem str83G4_d1_sup_d2_le_normalizer_y_inf_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    d.D1 ⊔ d.D2 ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) :
        Set G) := by
  intro h hh
  have hhP : h ∈ P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (str83G4Data_sup_le_bigB d hh)
  exact A4.mem_normalizer_inf (A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hhP)
    (F7.normalizer_le_normalizer_centralizer _ (le_normalizer_str83X L1 L2 S hhP)))
    (F7.normalizer_le_normalizer_centralizer _ ((str83G4_d1_sup_d2_le_normalizer hfr d).2.1 hh))

theorem str83G4_w_mem_normalizer_y_inf_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    d.w ∈ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) :
        Set G) := by
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  set Y0 := str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) with hY0def
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hwP : d.w ∈ P2 L1 L2 S := hL2P d.hwH2
  have hw2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hw2P : (d.w * d.w)⁻¹ ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr ((Q2 L1 L2 S).inv_mem hw2)))
  have hXXw : ∀ x ∈ X, d.w⁻¹ * x * d.w ∈ Xw := fun x hx => by
    rw [hXwdef, CFSG.mem_conjugate_iff]
    rwa [show d.w * (d.w⁻¹ * x * d.w) * d.w⁻¹ = x by group]
  have hXwX : ∀ t ∈ Xw, d.w⁻¹ * t * d.w ∈ X := fun t ht => by
    rw [hXwdef, CFSG.mem_conjugate_iff] at ht
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hw2P) _).mp ht
    rwa [show (d.w * d.w)⁻¹ * (d.w * t * d.w⁻¹) * (d.w * d.w)⁻¹⁻¹ = d.w⁻¹ * t * d.w by group] at h
  have hfwd : ∀ y ∈ Y0, d.w * y * d.w⁻¹ ∈ Y0 := by
    intro y hy
    obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyQ2 : d.w * y * d.w⁻¹ ∈ Q2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P2 L1 L2 S) hwP) y).mp
        (str83G4_y_le_q2 hfr hyY)
    have hCX : d.w * y * d.w⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have h := Subgroup.mem_centralizer_iff.mp hyC _ (hXXw x hx)
      calc x * (d.w * y * d.w⁻¹) = d.w * ((d.w⁻¹ * x * d.w) * y) * d.w⁻¹ := by group
        _ = d.w * (y * (d.w⁻¹ * x * d.w)) * d.w⁻¹ := by rw [h]
        _ = d.w * y * d.w⁻¹ * x := by group
    have hCXw : d.w * y * d.w⁻¹ ∈ Subgroup.centralizer (Xw : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
      have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyY).2 _ (hXwX t ht)
      calc t * (d.w * y * d.w⁻¹) = d.w * ((d.w⁻¹ * t * d.w) * y) * d.w⁻¹ := by group
        _ = d.w * (y * (d.w⁻¹ * t * d.w)) * d.w⁻¹ := by rw [h]
        _ = d.w * y * d.w⁻¹ * t := by group
    have hQ1 : d.w * y * d.w⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_inf.mp (str83G4_centralizer_x_le hfr (str83G4_not_le_normalizer_z2 hfr)
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (str83G4_q2_le_s hfr hyQ2), hCX⟩))).1
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hQ1, hCX⟩, hCXw⟩
  have hbwd : ∀ y ∈ Y0, d.w⁻¹ * y * d.w ∈ Y0 := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp (str83G4_q2_le_normalizer_y_inf_centralizer hfr d
      ((Q2 L1 L2 S).inv_mem hw2)) _).mp (hfwd y hy)
    rwa [show (d.w * d.w)⁻¹ * (d.w * y * d.w⁻¹) * (d.w * d.w)⁻¹⁻¹ = d.w⁻¹ * y * d.w by
      group] at h
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hfwd y, fun hy => ?_⟩
  have h := hbwd _ hy
  rwa [show d.w⁻¹ * (d.w * y * d.w⁻¹) * d.w = y by group] at h

theorem str83G4_commutator_mem_x_inf_of_mem_y_inf_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hW : d.D1 ⊔ CFSG.conjugate d.D1 d.w = d.D1 ⊔ d.D2) :
    ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  set Y0 := str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) with hY0def
  set I := X ⊓ Xw with hIdef
  have hHP : d.D1 ⊔ d.D2 ≤ P1 L1 L2 S :=
    (str83G4Data_sup_le_bigB d).trans (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
  have hHY0 := str83G4_d1_sup_d2_le_normalizer_y_inf_centralizer hfr d
  have hHI : ∀ h ∈ d.D1 ⊔ d.D2, ∀ i ∈ I, h * i * h⁻¹ ∈ I := fun h hh i hi =>
    (Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_inf (le_normalizer_str83X L1 L2 S (hHP hh))
      ((str83G4_d1_sup_d2_le_normalizer hfr d).2.1 hh)) i).mp hi
  have hw2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hw2P : (d.w * d.w)⁻¹ ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr ((Q2 L1 L2 S).inv_mem hw2)))
  have hwI : ∀ i ∈ I, d.w⁻¹ * i * d.w ∈ I := by
    intro i hi
    obtain ⟨hiX, hiXw⟩ := Subgroup.mem_inf.mp hi
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hXwdef, CFSG.mem_conjugate_iff] at hiXw
      have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hw2P) _).mp hiXw
      rwa [show (d.w * d.w)⁻¹ * (d.w * i * d.w⁻¹) * (d.w * d.w)⁻¹⁻¹ = d.w⁻¹ * i * d.w by
        group] at h
    · rw [hXwdef, CFSG.mem_conjugate_iff]
      rwa [show d.w * (d.w⁻¹ * i * d.w) * d.w⁻¹ = i by group]
  have hwY0 := str83G4_w_mem_normalizer_y_inf_centralizer hfr d
  let K : Subgroup G :=
    { carrier := {h | h ∈ d.D1 ⊔ d.D2 ∧ ∀ y ∈ Y0, h * y * h⁻¹ * y⁻¹ ∈ I}
      mul_mem' := by
        rintro h₁ h₂ ⟨hh₁, k₁⟩ ⟨hh₂, k₂⟩
        refine ⟨(d.D1 ⊔ d.D2).mul_mem hh₁ hh₂, fun y hy => ?_⟩
        have e : h₁ * h₂ * y * (h₁ * h₂)⁻¹ * y⁻¹ =
            h₁ * (h₂ * y * h₂⁻¹ * y⁻¹) * h₁⁻¹ * (h₁ * y * h₁⁻¹ * y⁻¹) := by
          group
        rw [e]
        exact I.mul_mem (hHI h₁ hh₁ _ (k₂ y hy)) (k₁ y hy)
      one_mem' := ⟨(d.D1 ⊔ d.D2).one_mem, fun y _ => by
        rw [show (1 : G) * y * 1⁻¹ * y⁻¹ = 1 by group]
        exact I.one_mem⟩
      inv_mem' := by
        rintro h ⟨hh, k⟩
        refine ⟨(d.D1 ⊔ d.D2).inv_mem hh, fun y hy => ?_⟩
        have hy' : h⁻¹ * y * h⁻¹⁻¹ ∈ Y0 :=
          (Subgroup.mem_normalizer_iff.mp (hHY0 ((d.D1 ⊔ d.D2).inv_mem hh)) y).mp hy
        have h1 := I.inv_mem (k _ hy')
        rwa [show (h * (h⁻¹ * y * h⁻¹⁻¹) * h⁻¹ * (h⁻¹ * y * h⁻¹⁻¹)⁻¹)⁻¹ =
          h⁻¹ * y * h⁻¹⁻¹ * y⁻¹ by group] at h1 }
  have hKmem : ∀ h, h ∈ K ↔ h ∈ d.D1 ⊔ d.D2 ∧ ∀ y ∈ Y0, h * y * h⁻¹ * y⁻¹ ∈ I :=
    fun _ => Iff.rfl
  have hC2 := str83G4_commutator_y_oTwoUpper_le hfr d hX hB
  have hD1K : d.D1 ≤ K := by
    intro e he
    refine (hKmem e).mpr ⟨Subgroup.mem_sup_left he, fun y hy => ?_⟩
    have heL : e ∈ L1 ⊔ S := Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 he))
    have heodd : Odd (orderOf e) :=
      Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 he)
    have hyX : y * e * y⁻¹ * e⁻¹ ∈ X := hC2 (Subgroup.commutator_mem_commutator
      (Subgroup.mem_inf.mp hy).1 (mem_oTwoUpper_of_odd heL heodd))
    have hX' : e * y * e⁻¹ * y⁻¹ ∈ X := by
      have h := X.inv_mem hyX
      rwa [show (y * e * y⁻¹ * e⁻¹)⁻¹ = e * y * e⁻¹ * y⁻¹ by group] at h
    have hY0' : e * y * e⁻¹ * y⁻¹ ∈ Y0 := Y0.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hHY0 (Subgroup.mem_sup_left he)) y).mp hy) (Y0.inv_mem hy)
    have hmem : e * y * e⁻¹ * y⁻¹ ∈ X ⊓ Subgroup.centralizer (Xw : Set G) :=
      Subgroup.mem_inf.mpr ⟨hX', (Subgroup.mem_inf.mp hY0').2⟩
    rwa [hXI] at hmem
  have hD1wK : CFSG.conjugate d.D1 d.w ≤ K := by
    intro x hx
    have hxH : x ∈ d.D1 ⊔ d.D2 := by rw [← hW]; exact Subgroup.mem_sup_right hx
    refine (hKmem x).mpr ⟨hxH, fun y hy => ?_⟩
    rw [CFSG.mem_conjugate_iff] at hx
    have hy' : d.w * y * d.w⁻¹ ∈ Y0 := (Subgroup.mem_normalizer_iff.mp hwY0 y).mp hy
    have h := hwI _ (((hKmem _).mp (hD1K hx)).2 _ hy')
    rwa [show d.w⁻¹ * (d.w * x * d.w⁻¹ * (d.w * y * d.w⁻¹) * (d.w * x * d.w⁻¹)⁻¹ *
      (d.w * y * d.w⁻¹)⁻¹) * d.w = x * y * x⁻¹ * y⁻¹ by group] at h
  have hHK : d.D1 ⊔ d.D2 ≤ K := by rw [← hW]; exact sup_le hD1K hD1wK
  exact fun h hh => ((hKmem h).mp (hHK hh)).2


private theorem str83G4_commutator_y_commute
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    {y₁ y₂ t : G} (hy₁ : y₁ ∈ str83Y L1 L2 S) (hy₂ : y₂ ∈ str83Y L1 L2 S)
    (ht : t ∈ CFSG.conjugate (str83X L1 L2 S) d.w) :
    (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t = t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by
  set X := str83X L1 L2 S with hXdef
  set Y := str83Y L1 L2 S with hYdef
  have hXc : ∀ x ∈ X, ∀ z ∈ X, x * z = z * x := fun x hx z hz => by
    simpa using hX.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨z, hz⟩ : ↥X)
  have hYX : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y := fun y hy x hx =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x hx).symm
  have hC23 := str83G4_commutator_y_conjugate_x_le hfr d hX hB
  obtain ⟨f, hf⟩ : ∃ f : G → G, ∀ y, f y = y * t * y⁻¹ * t⁻¹ := ⟨_, fun _ => rfl⟩
  have hfX : ∀ y ∈ Y, f y ∈ X := fun y hy => by
    rw [hf]; exact (Subgroup.mem_inf.mp (hC23 (Subgroup.commutator_mem_commutator hy ht))).1
  have hmul : ∀ u ∈ Y, ∀ v ∈ Y, f (u * v) = f v * f u := by
    intro u hu v hv
    have e : f (u * v) = (u * f v * u⁻¹) * f u := by simp only [hf]; group
    have hv' : u * f v * u⁻¹ = f v := by rw [hYX u hu (f v) (hfX v hv)]; group
    rw [e, hv']
  have hone : f 1 = 1 := by rw [hf]; group
  have hinv : ∀ u ∈ Y, f u⁻¹ = (f u)⁻¹ := by
    intro u hu
    have h := hmul u hu u⁻¹ (Y.inv_mem hu)
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hc : f (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) = 1 := by
    have h12 : y₁ * y₂ ∈ Y := Y.mul_mem hy₁ hy₂
    have h121 : y₁ * y₂ * y₁⁻¹ ∈ Y := Y.mul_mem h12 (Y.inv_mem hy₁)
    rw [hmul _ h121 _ (Y.inv_mem hy₂), hmul _ h12 _ (Y.inv_mem hy₁), hmul _ hy₁ _ hy₂,
      hinv _ hy₂, hinv _ hy₁, hXc _ (hfX y₂ hy₂) _ (hfX y₁ hy₁)]
    group
  rw [hf] at hc
  calc (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t =
      ((y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)⁻¹ * t⁻¹) * t *
        (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
    _ = t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by rw [hc, one_mul]

theorem str83G4_commutator_y_mem_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ y₁ ∈ str83Y L1 L2 S, ∀ y₂ ∈ str83Y L1 L2 S, ∀ g ∈ L1 ⊔ S,
      y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Subgroup.centralizer
        (CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) g : Set G) := by
  intro y₁ hy₁ y₂ hy₂ g hg
  have hYn := str83G4_isNormalIn_y hfr
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  rw [SetLike.mem_coe, CFSG.mem_conjugate_iff] at ht
  have h := str83G4_commutator_y_commute hfr d hX hB (hYn.2 g hg y₁ hy₁) (hYn.2 g hg y₂ hy₂) ht
  have e1 : (g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) * (g * y₁ * g⁻¹)⁻¹ * (g * y₂ * g⁻¹)⁻¹ *
      (g * t * g⁻¹) = g * ((y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t) * g⁻¹ := by group
  have e2 : (g * t * g⁻¹) * ((g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) * (g * y₁ * g⁻¹)⁻¹ *
      (g * y₂ * g⁻¹)⁻¹) = g * (t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)) * g⁻¹ := by group
  rw [e1, e2] at h
  exact (mul_left_cancel (mul_right_cancel h)).symm

theorem str83G4_commutator_y_y_le_z1
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) :
    ⁅str83Y L1 L2 S, str83Y L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  refine Subgroup.commutator_le.mpr fun y₁ hy₁ y₂ hy₂ => ?_
  rw [commutatorElement_def]
  set Y := str83Y L1 L2 S with hYdef
  exact str83G4_mem_z1_of_forall_centralizer hfr d hX hB hY5 hZ2 hδ₂ hXstep hIL2
    (Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂))
    (str83G4_commutator_y_mem_centralizer hfr d hX hB y₁ hy₁ y₂ hy₂)

theorem str83G4_commutator_y_q1_le
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hQstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S)) :
    ⁅str83Y L1 L2 S, Q1 L1 L2 S⁆ ≤ str83X L1 L2 S := by
  have hfr' := hfr
  obtain ⟨hF, hBS, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hBS ha hSz hL2 hZI
  set X := str83X L1 L2 S with hXdef
  set Y := str83Y L1 L2 S with hYdef
  have hYn := str83G4_isNormalIn_y hfr'
  have hLP : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  have hQP : Q1 L1 L2 S ≤ P1 L1 L2 S := pCoreOf_le 2 (P1 L1 L2 S)
  have hQ1L : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr').trans le_sup_right
  have hNX : ∀ g ∈ P1 L1 L2 S, ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hg) x).mp hx
  have hNQ1 : ∀ g ∈ P1 L1 L2 S, ∀ u ∈ Q1 L1 L2 S, g * u * g⁻¹ ∈ Q1 L1 L2 S := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg) u).mp hu
  have hZ1X : Z1 L1 L2 S ≤ X := hZ1Z2.trans (z2_le_str83X L1 L2 S)
  have hYY := str83G4_commutator_y_y_le_z1 hfr' d hX hB hY5 hZ2 hδ₂ hXstep hIL2
  have hC2 := str83G4_commutator_y_oTwoUpper_le hfr' d hX hB
  have hOY : ∀ g ∈ oTwoUpper (L1 ⊔ S), ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ X := fun g hg y hy => by
    have h := X.inv_mem (hC2 (Subgroup.commutator_mem_commutator hy hg))
    rwa [commutatorElement_def, show (y * g * y⁻¹ * g⁻¹)⁻¹ = g * y * g⁻¹ * y⁻¹ by group] at h
  let M : Subgroup G :=
    { carrier := {u | u ∈ Q1 L1 L2 S ∧ ∀ y ∈ Y, u * y * u⁻¹ * y⁻¹ ∈ X}
      mul_mem' := by
        rintro u₁ u₂ ⟨hu₁, k₁⟩ ⟨hu₂, k₂⟩
        refine ⟨(Q1 L1 L2 S).mul_mem hu₁ hu₂, fun y hy => ?_⟩
        have e : u₁ * u₂ * y * (u₁ * u₂)⁻¹ * y⁻¹ =
            u₁ * (u₂ * y * u₂⁻¹ * y⁻¹) * u₁⁻¹ * (u₁ * y * u₁⁻¹ * y⁻¹) := by
          group
        rw [e]
        exact X.mul_mem (hNX u₁ (hQP hu₁) _ (k₂ y hy)) (k₁ y hy)
      one_mem' := ⟨(Q1 L1 L2 S).one_mem, fun y _ => by
        rw [show (1 : G) * y * 1⁻¹ * y⁻¹ = 1 by group]
        exact X.one_mem⟩
      inv_mem' := by
        rintro u ⟨hu, k⟩
        refine ⟨(Q1 L1 L2 S).inv_mem hu, fun y hy => ?_⟩
        have h := hNX u⁻¹ (hQP ((Q1 L1 L2 S).inv_mem hu)) _ (X.inv_mem (k y hy))
        rwa [show u⁻¹ * (u * y * u⁻¹ * y⁻¹)⁻¹ * u⁻¹⁻¹ = u⁻¹ * y * u⁻¹⁻¹ * y⁻¹ by group] at h }
  have hMmem : ∀ u, u ∈ M ↔ u ∈ Q1 L1 L2 S ∧ ∀ y ∈ Y, u * y * u⁻¹ * y⁻¹ ∈ X :=
    fun _ => Iff.rfl
  have hMn : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) M := by
    refine ⟨fun u hu => ((hMmem u).mp hu).1, fun g hg u hu => ?_⟩
    obtain ⟨hu, k⟩ := (hMmem u).mp hu
    refine (hMmem _).mpr ⟨hNQ1 g (hLP hg) u hu, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y := hYn.2 g⁻¹ ((L1 ⊔ S).inv_mem hg) y hy
    have h := hNX g (hLP hg) _ (k _ hy')
    rwa [show g * (u * (g⁻¹ * y * g⁻¹⁻¹) * u⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * u * g⁻¹ * y * (g * u * g⁻¹)⁻¹ * y⁻¹ by group] at h
  have hYM : Y ≤ M := fun y hy => (hMmem y).mpr ⟨hYn.1 hy, fun y' hy' => hZ1X (hYY
    (Subgroup.commutator_mem_commutator hy hy'))⟩
  rcases hQstep.2.2.2 M hMn hYM (fun u hu => ((hMmem u).mp hu).1) with hMY | hMQ
  ·
    exfalso
    apply str83G4_not_twoResidual_le_centralizerMod_y_q1 hfr' d hX
    rw [F6.twoResidual_eq_oTwoUpper]
    intro g hg
    have hgL : g ∈ L1 ⊔ S := oTwoUpper_le _ hg
    have hgN : g ∈ Subgroup.normalizer (Y : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hYn.2 g hgL y hy, fun hy => ?_⟩
      have h := hYn.2 g⁻¹ ((L1 ⊔ S).inv_mem hgL) _ hy
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
    refine ⟨hgL, hgN, fun u hu => ?_⟩
    have hguO : g * u * g⁻¹ * u⁻¹ ∈ oTwoUpper (L1 ⊔ S) := by
      have h1 : u * g⁻¹ * u⁻¹ ∈ oTwoUpper (L1 ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.le_normalizer_oTwoUpper _ (hQ1L hu))
          g⁻¹).mp ((oTwoUpper (L1 ⊔ S)).inv_mem hg)
      rw [show g * u * g⁻¹ * u⁻¹ = g * (u * g⁻¹ * u⁻¹) by group]
      exact (oTwoUpper (L1 ⊔ S)).mul_mem hg h1
    have hguM : g * u * g⁻¹ * u⁻¹ ∈ M := (hMmem _).mpr
      ⟨(Q1 L1 L2 S).mul_mem (hNQ1 g (hLP hgL) u hu) ((Q1 L1 L2 S).inv_mem hu),
        fun y hy => hOY _ hguO y hy⟩
    rw [hMY] at hguM
    exact hguM
  · refine Subgroup.commutator_le.mpr fun y hy u hu => ?_
    have huM : u ∈ M := by rw [hMQ]; exact hu
    have h := X.inv_mem (((hMmem u).mp huM).2 y hy)
    rw [commutatorElement_def]
    rwa [show (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ by group] at h

theorem str83G4_commutator_mem_x_of_mem_y
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
        h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hQstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S)) :
    ∀ g ∈ L1 ⊔ S, ∀ y ∈ str83Y L1 L2 S, g * y * g⁻¹ * y⁻¹ ∈ str83X L1 L2 S := by
  set X := str83X L1 L2 S with hXdef
  have hQ1L : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hC2 := str83G4_commutator_y_oTwoUpper_le hfr d hX hB
  have hYQ := str83G4_commutator_y_q1_le hfr d hX hB hY5 hZ2 hδ₂ hXstep hIL2 hQstep
  have hQN : Q1 L1 L2 S ≤ Subgroup.normalizer (oTwoUpper (L1 ⊔ S) : Set G) :=
    hQ1L.trans (CFSG.Quasithin.le_normalizer_oTwoUpper _)
  intro g hg y hy
  rw [← str83G4_oTwoUpper_sup_left hfr d] at hg
  obtain ⟨o, ho, u, hu, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQN).mp hg
  have hoP : o ∈ P1 L1 L2 S := sup_left_le_p1 L1 L2 S (oTwoUpper_le _ ho)
  have h1 : u * y * u⁻¹ * y⁻¹ ∈ X := by
    have h := X.inv_mem (hYQ (Subgroup.commutator_mem_commutator hy hu))
    rwa [commutatorElement_def, show (y * u * y⁻¹ * u⁻¹)⁻¹ = u * y * u⁻¹ * y⁻¹ by group] at h
  have h2 : o * y * o⁻¹ * y⁻¹ ∈ X := by
    have h := X.inv_mem (hC2 (Subgroup.commutator_mem_commutator hy ho))
    rwa [commutatorElement_def, show (y * o * y⁻¹ * o⁻¹)⁻¹ = o * y * o⁻¹ * y⁻¹ by group] at h
  have h3 : o * (u * y * u⁻¹ * y⁻¹) * o⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hoP) _).mp h1
  rw [show o * u * y * (o * u)⁻¹ * y⁻¹ = o * (u * y * u⁻¹ * y⁻¹) * o⁻¹ * (o * y * o⁻¹ * y⁻¹) by
    group]
  exact X.mul_mem h3 h2

theorem str83G4_y_inf_centralizer_eq_of_leaves
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hW : d.D1 ⊔ CFSG.conjugate d.D1 d.w = d.D1 ⊔ d.D2)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hD1I : ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    (hQstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S)) :
    str83Y L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  have hY5 := str83G4_commutator_mem_x_inf_of_mem_y_inf_centralizer hfr d hX hB hXI hW
  exact str83G4_y_inf_centralizer_eq hfr d hX hB (str83G4_q2_le_normalizer_y_inf_centralizer hfr d)
    hY5 (str83G4_commutator_mem_x_of_mem_y hfr d hX hB hY5 hZ2 hδ₂ hXstep hIL2 hQstep)
    (fun f hf hfN => str83G4_mem_z1_of_forall_centralizer hfr d hX hB hY5 hZ2 hδ₂ hXstep hIL2 hf
      hfN) hXstep hXI hIL2 hD1I hZ2 hδ₂

end CFSG.Quasithin.Stroth

end
