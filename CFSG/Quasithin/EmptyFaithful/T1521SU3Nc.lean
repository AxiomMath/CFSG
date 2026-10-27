module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Bor
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Cyc
public import CFSG.Quasithin.EmptyFaithful.T1521SU3ZcG

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open CFSG.ProperTwoGeneratedCore.RootCenter

variable {G : Type} [Group G]

theorem conj_mem_inf_iff {S L : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g ∈ S) (x : ↥L) : g * (x : G) * g⁻¹ ∈ S ⊓ L ↔ (x : G) ∈ S ⊓ L := by
  constructor
  · intro h
    refine ⟨?_, x.2⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem hg) h.1) hg
    simpa [mul_assoc] using this
  · intro h
    exact ⟨S.mul_mem (S.mul_mem hg h.1) (S.inv_mem hg),
      (Subgroup.mem_normalizer_iff.mp (hSN hg) x).mp x.2⟩

theorem conjAut_mem_autStab {S L : Subgroup G} (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∈ S) :
    conjAut L g (hSN hg) ∈ autStab ((A4.toSylow hSyl : Sylow 2 ↥L) : Subgroup ↥L) := by
  rw [mem_autStab]
  intro x
  change ((conjAut L g (hSN hg) x : ↥L) : G) ∈ S ⊓ L ↔ (x : G) ∈ S ⊓ L
  rw [coe_conjAut_apply]
  exact conj_mem_inf_iff hSN hg x

theorem coe_mem_normalizer_inf {S L : Subgroup G} (hSyl : IsSylowTwoOf (S ⊓ L) L) {w : ↥L}
    (hw : w ∈ Subgroup.normalizer (((A4.toSylow hSyl : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L)) :
    (w : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhL : h ∈ L := hSyl.1 hh
    have := (Subgroup.mem_normalizer_iff.mp hw ⟨h, hhL⟩).mp hh
    exact this
  · intro hh
    have hhL : (w : G) * h * (w : G)⁻¹ ∈ L := hSyl.1 hh
    have hhL' : h ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem w.2) hhL) w.2
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hw ⟨h, hhL'⟩).mpr hh

variable [Finite G]

theorem nc1521U3 {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSU 3 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ B₀ : Subgroup G, B₀ ≤ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      B₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) ∧ oTwoUpper B₀ = B₀ ∧
      ∀ v ∈ S, (∀ b ∈ B₀, v * b = b * v) → ∀ l ∈ L, v * l = l * v := by
  classical
  obtain ⟨b, hbS, hb2, hcover⟩ := exists_involution_cover hn hL hSyl hS2 hSN
  set R : Subgroup G := S ⊓ L with hRdef
  set R' : Sylow 2 ↥L := A4.toSylow hSyl with hR'
  have hR'mem : ∀ x : ↥L, x ∈ (R' : Subgroup ↥L) ↔ (x : G) ∈ R := fun x => Iff.rfl
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hSN hbS
  set β : MulAut ↥L := conjAut L b hbN with hβ
  have hβstab : β ∈ autStab (R' : Subgroup ↥L) := conjAut_mem_autStab hSyl hSN hbS
  have hβ2 : β ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hβ, coe_conjAut_apply, coe_conjAut_apply]
    have h1 : b * (b * (x : G) * b⁻¹) * b⁻¹ = (b * b) * (x : G) * (b * b)⁻¹ := by group
    rw [h1, ← pow_two, hb2]
    group
  obtain ⟨r, w, hgood⟩ := exists_goodElt hn hL R' hβstab hβ2
  have hrR : (r : G) ∈ R := hgood.r_mem
  have hrS : (r : G) ∈ S := hrR.1
  set b' : G := (r : G)⁻¹ * b with hb'
  have hb'S : b' ∈ S := S.mul_mem (S.inv_mem hrS) hbS
  have hfixG : b' * (w : G) * b'⁻¹ = w := by
    have := congrArg (fun x : ↥L => (x : G)) hgood.fix
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply, hβ,
      coe_conjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [hb']
    calc (r : G)⁻¹ * b * (w : G) * ((r : G)⁻¹ * b)⁻¹ = (r : G)⁻¹ * (b * (w : G) * b⁻¹) * r := by
          group
      _ = w := this
  have hcomm : b' * (w : G) = (w : G) * b' := by
    calc b' * (w : G) = (b' * (w : G) * b'⁻¹) * b' := by group
      _ = (w : G) * b' := by rw [hfixG]
  set T : Subgroup G := innerPart1521 S L with hT
  have hTS : T ≤ S := innerPart1521_le S L
  have hRT : R ≤ T := le_sup_left
  set S₁ : Subgroup G := T ⊔ Subgroup.zpowers b' with hS₁
  have hS₁S : S₁ ≤ S := sup_le hTS (Subgroup.zpowers_le.mpr hb'S)
  have hJS₁ : thompsonJ S ≤ S₁ := by
    refine iSup₂_le fun A hA a ha => ?_
    have haS : a ∈ S := hA.1 ha
    have ha2 : a ^ 2 = 1 := hA.2.1.2 a ha
    rcases hcover a haS ha2 with h | h
    · exact Subgroup.mem_sup_left h
    · have hae : a = (r : G) * b' * (b⁻¹ * a) := by rw [hb']; group
      rw [hae]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hRT hrR))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))) (Subgroup.mem_sup_left h)
  have hJeq : thompsonJ S₁ = thompsonJ S := B6.thompsonJ_eq_of_le hJS₁ hS₁S
  set N₁ : Subgroup G := (L ⊓ Subgroup.normalizer (R : Set G)) ⊓ Subgroup.normalizer (S₁ : Set G)
    with hN₁
  have hwL : (w : G) ∈ L := w.2
  have hwR : (w : G) ∈ Subgroup.normalizer (R : Set G) :=
    coe_mem_normalizer_inf hSyl hgood.w_norm
  have hwT : ∀ x ∈ T, (w : G) * x * (w : G)⁻¹ ∈ T := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (borel_le_normalizer_innerPart S L ⟨hwL, hwR⟩) x).mp hx
  have hwS₁ : (w : G) ∈ Subgroup.normalizer (S₁ : Set G) := by
    apply A4.mem_normalizer_of_conj_mem
    intro x hx
    refine conj_mem_sup_aux hwT (fun y hy => ?_) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (w : G) b' := hcomm.symm
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b') k
  have hwN₁ : (w : G) ∈ N₁ := ⟨⟨hwL, hwR⟩, hwS₁⟩
  have hRN₁ : R ≤ N₁ := fun s hs =>
    ⟨⟨hSyl.1 hs, Subgroup.le_normalizer hs⟩,
      Subgroup.le_normalizer (Subgroup.mem_sup_left (hRT hs) : s ∈ S₁)⟩
  have hwodd : Odd (orderOf (w : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hgood.w_odd
  set B₀ : Subgroup G := oTwoUpper N₁ with hB₀
  have hwB₀ : (w : G) ∈ B₀ := mem_oTwoUpper_of_odd hwN₁ hwodd
  have hRB₀ : R ≤ B₀ := by
    intro c hc
    have hcL : c ∈ L := hSyl.1 hc
    obtain ⟨s, hs, hsc⟩ := hgood.surj ⟨c, hcL⟩ ((hR'mem _).2 hc)
    have hsc' : (s : G)⁻¹ * (w : G) * (s : G) * (w : G)⁻¹ = c := by
      have := congrArg (fun x : ↥L => (x : G)) hsc
      simpa using this
    have hsR : (s : G) ∈ R := (hR'mem s).1 hs
    have h1 : (s : G)⁻¹ * (w : G) * (s : G) ∈ N₁ :=
      N₁.mul_mem (N₁.mul_mem (N₁.inv_mem (hRN₁ hsR)) hwN₁) (hRN₁ hsR)
    have h2 : Odd (orderOf ((s : G)⁻¹ * (w : G) * (s : G))) := by
      have : (s : G)⁻¹ * (w : G) * (s : G) = (MulAut.conj (s : G)⁻¹) (w : G) := by
        simp
      rw [this, MulEquiv.orderOf_eq]
      exact hwodd
    have h3 : (s : G)⁻¹ * (w : G) * (s : G) ∈ B₀ := mem_oTwoUpper_of_odd h1 h2
    rw [← hsc']
    exact B₀.mul_mem h3 (B₀.inv_mem hwB₀)
  refine ⟨B₀, (oTwoUpper_le N₁).trans inf_le_left, ?_, oTwoUpper_oTwoUpper1521 N₁, ?_⟩
  · intro g hg
    have h1 : g ∈ Subgroup.normalizer (S₁ : Set G) := ((oTwoUpper_le N₁) hg).2
    have h2 := normalizer_le_normalizer_thompsonJ S₁ h1
    rwa [hJeq] at h2
  · intro v hvS hvc l hl
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hSN hvS
    set α : MulAut ↥L := conjAut L v hvN with hα
    have hαstab : α ∈ autStab (R' : Subgroup ↥L) := conjAut_mem_autStab hSyl hSN hvS
    have hαfix : ∀ x ∈ (R' : Subgroup ↥L), α x = x := by
      intro x hx
      apply Subtype.ext
      rw [hα, coe_conjAut_apply]
      have := hvc _ (hRB₀ ((hR'mem x).1 hx))
      calc v * (x : G) * v⁻¹ = (x : G) * v * v⁻¹ := by rw [this]
        _ = x := by group
    have hRC := rootCenterData_of_isPSU hn hL R'
    have hUR : omegaU (R' : Subgroup ↥L) ≤ (R' : Subgroup ↥L) := fun x hx =>
      ((hRC.center_iff x).1 hx).1
    have hαA : α ∈ rootCenterAut (R' : Subgroup ↥L) (omegaU (R' : Subgroup ↥L)) :=
      ⟨map_eq_iff_aux.mpr (mem_autStab.mp hαstab), fun u hu => hαfix u (hUR hu)⟩
    obtain ⟨z, hz, hαz⟩ := hRC.fix_eq α hαA hαfix
    have hzR : z ∈ (R' : Subgroup ↥L) := hUR hz
    have hαw : α w = w := by
      apply Subtype.ext
      rw [hα, coe_conjAut_apply]
      have := hvc _ hwB₀
      calc v * (w : G) * v⁻¹ = (w : G) * v * v⁻¹ := by rw [this]
        _ = w := by group
    have hzw : w * z = z * w := by
      rw [hαz, MulAut.conj_apply] at hαw
      exact (mul_inv_eq_iff_eq_mul.mp hαw).symm
    have hz1 : z = 1 := hgood.centr z hzR hzw
    have hα1 : α = 1 := by rw [hαz, hz1, map_one]
    have := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : G)) hα1
    simp only [hα, coe_conjAut_apply, MulAut.one_apply] at this
    calc v * l = (v * l * v⁻¹) * v := by group
      _ = l * v := by rw [this]

end CFSG.Quasithin.U31521
