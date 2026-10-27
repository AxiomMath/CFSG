module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_closure_le_of_forall {A S : Subgroup G} {s : Set G}
    (hS : s ⊆ Subgroup.normalizer (S : Set G)) (hA : ∀ a ∈ A, ∀ y ∈ s, ⁅a, y⁆ ∈ S) :
    ⁅A, Subgroup.closure s⁆ ≤ S := by
  have hnorm : Subgroup.closure s ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.closure_le _).mpr hS
  apply Subgroup.commutator_le.mpr
  intro a ha g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy => exact hA a ha y hy
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hxn : x ∈ Subgroup.normalizer (S : Set G) := hnorm hx
      have hconj : x * ⁅a, y⁆ * x⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hxn ⁅a, y⁆).mp ihy
      rw [commutatorElement_mul_right_eq_mul_conj]
      exact (by simpa only [mul_assoc] using S.mul_mem ihx hconj)
  | inv x hx ihx =>
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).inv_mem (hnorm hx)
      rw [commutatorElement_inv_right]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hxinv ⁅x, a⁆).mp (by simpa using S.inv_mem ihx)

private theorem seven_twelve_mod_conj_mem_commutator {A B P : Subgroup G} {x : G}
    (hA : P ≤ Subgroup.normalizer (A : Set G)) (hB : P ≤ Subgroup.normalizer (B : Set G))
    (hx : x ∈ P) : ∀ c ∈ ⁅A, B⁆, x * c * x⁻¹ ∈ ⁅A, B⁆ := by
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have hxa : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hA hx) a).mp ha
      have hxb : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hB hx) b).mp hb
      rw [conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator hxa hxb
  | one => simp
  | mul c d hc hd ihc ihd =>
      have hcd : x * (c * d) * x⁻¹ = (x * c * x⁻¹) * (x * d * x⁻¹) := by group
      rw [hcd]
      exact Subgroup.mul_mem _ ihc ihd
  | inv c hc ihc =>
      have hci : x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := by group
      rw [hci]
      exact Subgroup.inv_mem _ ihc

theorem le_normalizer_commutator_of_le_of_le {P A B : Subgroup G}
    (hA : P ≤ Subgroup.normalizer (A : Set G)) (hB : P ≤ Subgroup.normalizer (B : Set G)) :
    P ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hxP
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact seven_twelve_mod_conj_mem_commutator hA hB hxP h hh
  · intro hh
    have hxinv : x⁻¹ ∈ P := P.inv_mem hxP
    have hconj := seven_twelve_mod_conj_mem_commutator hA hB hxinv (x * h * x⁻¹) hh
    convert hconj using 1
    group

private theorem seven_twelve_mod_commutator_commutator_mem {A X : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    {a x y : G} (ha : a ∈ A) (hx : x ∈ X) (hy : y ∈ X) :
    ⁅a, ⁅x, y⁆⁆ ∈ ⁅⁅A, X⁆, X⁆ := by
  have hPX : X ≤ Subgroup.normalizer (⁅A, X⁆ : Subgroup G) :=
    le_normalizer_commutator_of_le_of_le hXA (Subgroup.le_normalizer (H := X))
  have hNX : X ≤ Subgroup.normalizer (⁅⁅A, X⁆, X⁆ : Subgroup G) :=
    le_normalizer_commutator_of_le_of_le hPX (Subgroup.le_normalizer (H := X))
  have hNP : ⁅⁅A, X⁆, X⁆ ≤ ⁅A, X⁆ := by
    have h := Subgroup.le_normalizer_iff_commutator_le_right.mp hPX
    rwa [Subgroup.commutator_comm X ⁅A, X⁆] at h
  have hPA : ⁅A, X⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hXA
  have hNA : ⁅⁅A, X⁆, X⁆ ≤ A := hNP.trans hPA
  have hn1 : ⁅x⁻¹, ⁅y⁻¹, a⁆⁆ ∈ ⁅⁅A, X⁆, X⁆ := by
    have hin : ⁅y⁻¹, a⁆ ∈ ⁅A, X⁆ := by
      have h := Subgroup.commutator_mem_commutator (X.inv_mem hy) ha
      rwa [Subgroup.commutator_comm X A] at h
    have h := Subgroup.commutator_mem_commutator (X.inv_mem hx) hin
    rwa [Subgroup.commutator_comm X ⁅A, X⁆] at h
  have ht2 : y * ⁅x⁻¹, ⁅y⁻¹, a⁆⁆ * y⁻¹ ∈ ⁅⁅A, X⁆, X⁆ :=
    (Subgroup.mem_normalizer_iff.mp (hNX hy) ⁅x⁻¹, ⁅y⁻¹, a⁆⁆).mp hn1
  have hn2 : ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ ∈ ⁅⁅A, X⁆, X⁆ := by
    have hin : ⁅a⁻¹, x⁻¹⁆ ∈ ⁅A, X⁆ :=
      Subgroup.commutator_mem_commutator (A.inv_mem ha) (X.inv_mem hx)
    have h := Subgroup.commutator_mem_commutator hy hin
    rwa [Subgroup.commutator_comm X ⁅A, X⁆] at h
  have ht3 : a * ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ * a⁻¹ ∈ ⁅⁅A, X⁆, X⁆ := by
    have hn2A : ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ ∈ A := hNA hn2
    have hcomm : a * ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ * a⁻¹ = ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ := by
      rw [hAab a ha ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ hn2A, mul_assoc, mul_inv_cancel, mul_one]
    rw [hcomm]
    exact hn2
  have hw : (x⁻¹ * ⁅a, ⁅x, y⁆⁆ * x) * (y * ⁅x⁻¹, ⁅y⁻¹, a⁆⁆ * y⁻¹)
      * (a * ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ * a⁻¹) = 1 := by
    simpa only [inv_inv, mul_assoc] using
      conj_commutatorElement_right_commutatorElement_mul a x⁻¹ y
  have hu : x⁻¹ * ⁅a, ⁅x, y⁆⁆ * x ∈ ⁅⁅A, X⁆, X⁆ := by
    have hprod : (y * ⁅x⁻¹, ⁅y⁻¹, a⁆⁆ * y⁻¹) * (a * ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ * a⁻¹)
        ∈ ⁅⁅A, X⁆, X⁆ := Subgroup.mul_mem _ ht2 ht3
    have hw' : (x⁻¹ * ⁅a, ⁅x, y⁆⁆ * x)
        * ((y * ⁅x⁻¹, ⁅y⁻¹, a⁆⁆ * y⁻¹) * (a * ⁅y, ⁅a⁻¹, x⁻¹⁆⁆ * a⁻¹)) = 1 := by
      rwa [mul_assoc] at hw
    rw [mul_eq_one_iff_eq_inv.mp hw']
    exact Subgroup.inv_mem _ hprod
  have hxN : x ∈ Subgroup.normalizer (⁅⁅A, X⁆, X⁆ : Subgroup G) := hNX hx
  have hfinal : x * (x⁻¹ * ⁅a, ⁅x, y⁆⁆ * x) * x⁻¹ ∈ ⁅⁅A, X⁆, X⁆ :=
    (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * ⁅a, ⁅x, y⁆⁆ * x)).mp hu
  convert hfinal using 1
  group

theorem commutator_commutator_eq_of_forall_inv_mul_mem {A X C : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hC : C ≤ Subgroup.centralizer (A : Set G)) (hX : ∀ x ∈ X, ∃ c ∈ ⁅X, X⁆, c⁻¹ * x ∈ C) :
    ⁅⁅A, X⁆, X⁆ = ⁅A, X⁆ := by
  have hPX : X ≤ Subgroup.normalizer (⁅A, X⁆ : Subgroup G) :=
    le_normalizer_commutator_of_le_of_le hXA (Subgroup.le_normalizer (H := X))
  have hNX : X ≤ Subgroup.normalizer (⁅⁅A, X⁆, X⁆ : Subgroup G) :=
    le_normalizer_commutator_of_le_of_le hPX (Subgroup.le_normalizer (H := X))
  apply le_antisymm
  · have h := Subgroup.le_normalizer_iff_commutator_le_right.mp hPX
    rwa [Subgroup.commutator_comm X ⁅A, X⁆] at h
  · have hkey : ∀ a ∈ A, ∀ z ∈ ⁅X, X⁆, ⁅a, z⁆ ∈ ⁅⁅A, X⁆, X⁆ := by
      have hsub : ∀ g ∈ ({g : G | ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ = g} : Set G),
          g ∈ Subgroup.normalizer (⁅⁅A, X⁆, X⁆ : Subgroup G) := by
        rintro g ⟨x, hx, y, hy, rfl⟩
        show x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (⁅⁅A, X⁆, X⁆ : Subgroup G)
        exact mul_mem (mul_mem (mul_mem (hNX hx) (hNX hy)) (inv_mem (hNX hx)))
          (inv_mem (hNX hy))
      have hgen : ∀ a ∈ A, ∀ y ∈ ({g : G | ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ = g} : Set G),
          ⁅a, y⁆ ∈ ⁅⁅A, X⁆, X⁆ := by
        rintro a ha g ⟨x, hx, y, hy, rfl⟩
        exact seven_twelve_mod_commutator_commutator_mem hAab hXA ha hx hy
      have h1 := commutator_closure_le_of_forall (A := A) (S := ⁅⁅A, X⁆, X⁆)
        (s := {g : G | ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ = g}) hsub hgen
      intro a ha z hz
      exact (Subgroup.commutator_le.mp h1) a ha z (by rwa [Subgroup.commutator_def] at hz)
    apply Subgroup.commutator_le.mpr
    intro a ha x hx
    obtain ⟨c, hc, hdC⟩ := hX x hx
    have hcd : ⁅a, c⁻¹ * x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp (hC hdC) a ha
    have hxd : x = c * (c⁻¹ * x) := by group
    rw [hxd, commutatorElement_mul_right_eq_mul_conj, hcd, mul_one]
    have hcN : ⁅a, c⁆ ∈ ⁅⁅A, X⁆, X⁆ := hkey a ha c hc
    convert hcN using 1
    group

theorem exists_mem_commutator_inv_mul_mem {K N X : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥K →* Q} (hφ : IsBarMap K N φ) (hXK : X ≤ K)
    (hperf : ⁅barSub K φ X, barSub K φ X⁆ = barSub K φ X) :
    ∀ x ∈ X, ∃ c ∈ ⁅X, X⁆, c⁻¹ * x ∈ N := by
  have hXmap : (X.subgroupOf K).map K.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK]
  have hsub : (⁅X, X⁆).subgroupOf K = ⁅X.subgroupOf K, X.subgroupOf K⁆ := by
    have h2 : (⁅X.subgroupOf K, X.subgroupOf K⁆).map K.subtype = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, hXmap]
    rw [← h2, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hmap : barSub K φ ⁅X, X⁆ = ⁅barSub K φ X, barSub K φ X⁆ := by
    unfold barSub
    rw [hsub, Subgroup.map_commutator]
  intro x hx
  have hxK : x ∈ K := hXK hx
  have hxbar : φ ⟨x, hxK⟩ ∈ barSub K φ ⁅X, X⁆ := by
    rw [hmap, hperf]
    exact mem_barSub.mpr ⟨⟨x, hxK⟩, hx, rfl⟩
  obtain ⟨c', hc'X, hc'eq⟩ := mem_barSub.mp hxbar
  refine ⟨(c' : G), hc'X, ?_⟩
  refine (hφ.ker_iff ⟨(c' : G)⁻¹ * x, K.mul_mem (K.inv_mem c'.2) hxK⟩).mp ?_
  have hsub2 : (⟨(c' : G)⁻¹ * x, K.mul_mem (K.inv_mem c'.2) hxK⟩ : ↥K)
      = (c')⁻¹ * ⟨x, hxK⟩ := by ext; rfl
  rw [hsub2, map_mul, map_inv, hc'eq, inv_mul_cancel]

theorem exists_eq_inv_mul_conj_of_inf_centralizer [Finite G] {B : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (B : Set G))
    (hfree : B ⊓ Subgroup.centralizer ({y} : Set G) = ⊥) :
    ∀ a ∈ B, ∃ q ∈ B, a = q⁻¹ * (y * q * y⁻¹) := by
  intro a ha
  have hconj : ∀ b ∈ B, y * b * y⁻¹ ∈ B := fun b hb => (mem_normalizer_iff.1 hy b).1 hb
  let φ : B → B := fun b => ⟨(b : G)⁻¹ * (y * b * y⁻¹), mul_mem (inv_mem b.2) (hconj b b.2)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have e : (b : G)⁻¹ * (y * b * y⁻¹) = (b' : G)⁻¹ * (y * b' * y⁻¹) :=
      congrArg Subtype.val hbb
    set c : G := (b' : G) * (b : G)⁻¹
    have hcB : c ∈ B := mul_mem b'.2 (inv_mem b.2)
    have hyc : y * c * y⁻¹ = c := by
      have hX := hconj b b.2
      have hX' := hconj b' b'.2
      have e1 : (b' : G) * ((b : G)⁻¹ * (y * b * y⁻¹)) = y * b' * y⁻¹ := by
        rw [e, mul_inv_cancel_left]
      have e2 : c * (y * b * y⁻¹) = y * b' * y⁻¹ := by
        rw [← e1, mul_assoc]
      have e3 : y * c * y⁻¹ = (y * b' * y⁻¹) * (y * b * y⁻¹)⁻¹ := by
        simp only [c]
        group
      rw [e3, ← e2, mul_inv_cancel_right]
    have hcC : c ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * y = y * c * y⁻¹ * y := by rw [hyc]
        _ = y * c := by group
    have hc1 : c = 1 := by
      have hmem : c ∈ (⊥ : Subgroup G) := hfree ▸ mem_inf.2 ⟨hcB, hcC⟩
      exact mem_bot.1 hmem
    refine Subtype.ext ?_
    have hbc : (b' : G) = b := by
      have := congrArg (· * (b : G)) hc1
      simpa [c] using this
    exact hbc.symm
  have : Finite B := inferInstance
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨a, ha⟩
  exact ⟨b, b.2, (congrArg Subtype.val hb).symm⟩

end CFSG.LocalAnalysis.WeakClosure81
