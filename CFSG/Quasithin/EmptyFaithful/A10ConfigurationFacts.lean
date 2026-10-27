module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

theorem forall_mem_baseSub {X Y : Subgroup S4} {lx ly : List S4} (hX : ∀ a, a ∈ X ↔ a ∈ lx)
    (hY : ∀ b, b ∈ Y ↔ b ∈ ly) {P : Wc → Prop}
    (h : ∀ a ∈ lx, ∀ b ∈ ly, P ⟨a, b, false⟩) : ∀ x ∈ baseSub X Y, P x := by
  rintro ⟨a, b, e⟩ ⟨he, ha, hb⟩
  have he' : e = false := he
  subst he'
  exact h a ((hX a).1 ha) b ((hY b).1 hb)

theorem forall_mem_symSub {X : Subgroup S4} {lx : List S4} (hX : ∀ a, a ∈ X ↔ a ∈ lx)
    {P : Wc → Prop} (h : ∀ a ∈ lx, ∀ b ∈ lx, ∀ e : Bool, P ⟨a, b, e⟩) : ∀ x ∈ symSub X, P x := by
  rintro ⟨a, b, e⟩ ⟨ha, hb⟩
  exact h a ((hX a).1 ha) b ((hX b).1 hb) e

theorem forall_mem_Th {P : Wc → Prop} (h : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool, P ⟨a, b, e⟩) :
    ∀ x ∈ Th, P x :=
  forall_mem_symSub (fun _ => Iff.rfl) h

theorem forall_mem_Jh {P : Wc → Prop} (h : ∀ a ∈ dList, ∀ b ∈ dList, P ⟨a, b, false⟩) :
    ∀ x ∈ Jh, P x :=
  forall_mem_baseSub (fun _ => Iff.rfl) (fun _ => Iff.rfl) h

theorem forall_mem_A3 {P : Wc → Prop} (h : ∀ a ∈ v'List, ∀ b ∈ vList, P ⟨a, b, false⟩) :
    ∀ x ∈ A3, P x :=
  forall_mem_baseSub (fun _ => Iff.rfl) (fun _ => Iff.rfl) h

theorem forall_mem_A4 {P : Wc → Prop} (h : ∀ a ∈ vList, ∀ b ∈ v'List, P ⟨a, b, false⟩) :
    ∀ x ∈ A4, P x :=
  forall_mem_baseSub (fun _ => Iff.rfl) (fun _ => Iff.rfl) h

theorem le_normalizer_of_forall {H K : Subgroup Wc}
    (h : ∀ w ∈ H, ∀ x ∈ K, w * x * w⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set Wc) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h w hw x hx
  · intro hx
    have := h w⁻¹ (H.inv_mem hw) _ hx
    simpa [mul_assoc] using this

def z0 : Wc := ⟨tau, tau, false⟩
def t0 : Wc := ⟨tau, 1, false⟩
def t0' : Wc := ⟨1, tau, false⟩
def s0 : Wc := ⟨1, 1, true⟩

theorem Th_isPGroup : IsPGroup 2 Th :=
  IsPGroup.of_card (n := 7) (by rw [card_Th]; norm_num)

theorem Th_index : Th.index = 9 := by
  have := Subgroup.card_mul_index Th
  rw [card_Th, card_Wc'] at this
  omega

theorem Th_not_dvd_index : ¬ 2 ∣ Th.index := by
  rw [Th_index]
  decide

@[expose] noncomputable def thSylow : Sylow 2 Wc :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Th_isPGroup.toSylow Th_not_dvd_index

theorem conj_of_e_false {w x : Wc} (hw : w.e = false) (hx : x.e = false) :
    w * x * w⁻¹ = ⟨w.a * x.a * w.a⁻¹, w.b * x.b * w.b⁻¹, false⟩ := by
  rcases w with ⟨a, b, e⟩
  rcases x with ⟨a', b', e'⟩
  simp only at hw hx
  subst hw hx
  rfl

theorem conj_of_e_true {w x : Wc} (hw : w.e = true) (hx : x.e = false) :
    w * x * w⁻¹ = ⟨w.a * x.b * w.a⁻¹, w.b * x.a * w.b⁻¹, false⟩ := by
  rcases w with ⟨a, b, e⟩
  rcases x with ⟨a', b', e'⟩
  simp only at hw hx
  subst hw hx
  rfl

theorem symSub_le_normalizer_baseSub {X Y : Subgroup S4}
    (hXY : ∀ a ∈ X, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) :
    symSub X ≤ Subgroup.normalizer (baseSub Y Y : Set Wc) := by
  have key : ∀ w ∈ symSub X, ∀ x ∈ baseSub Y Y, w * x * w⁻¹ ∈ baseSub Y Y := by
    intro w hw x hx
    obtain ⟨hxe, hxa, hxb⟩ := hx
    cases hwe : w.e
    · rw [conj_of_e_false hwe hxe]
      exact ⟨rfl, hXY _ hw.1 _ hxa, hXY _ hw.2 _ hxb⟩
    · rw [conj_of_e_true hwe hxe]
      exact ⟨rfl, hXY _ hw.1 _ hxb, hXY _ hw.2 _ hxa⟩
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key w hw x
  · intro hx
    have := key w⁻¹ ((symSub X).inv_mem hw) _ hx
    simpa [mul_assoc] using this

theorem A1_le_Jh : A1 ≤ Jh := baseSub_le_baseSub V_le_D V_le_D
theorem A2_le_Jh : A2 ≤ Jh := baseSub_le_baseSub V'_le_D V'_le_D
theorem A3_le_Jh : A3 ≤ Jh := baseSub_le_baseSub V'_le_D V_le_D
theorem A4_le_Jh : A4 ≤ Jh := baseSub_le_baseSub V_le_D V'_le_D

theorem Th_le_normalizer_Jh : Th ≤ Subgroup.normalizer (Jh : Set Wc) :=
  symSub_le_normalizer_baseSub (X := D) (Y := D) (by decide +kernel)

theorem Th_le_normalizer_A2 : Th ≤ Subgroup.normalizer (A2 : Set Wc) :=
  symSub_le_normalizer_baseSub (X := D) (Y := V') (by decide +kernel)

theorem A1_normal : A1.Normal := by
  have h : ∀ a ∈ (⊤ : Subgroup S4), ∀ y ∈ V, a * y * a⁻¹ ∈ V := by
    intro a _ y hy
    have : ∀ a : S4, ∀ y ∈ vList, a * y * a⁻¹ ∈ vList := by decide +kernel
    exact this a y hy
  have hle := symSub_le_normalizer_baseSub (X := ⊤) (Y := V) h
  refine ⟨fun x hx w => ?_⟩
  have hw : w ∈ symSub (⊤ : Subgroup S4) := ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  exact (Subgroup.mem_normalizer_iff.mp (hle hw) x).mp hx

theorem Th_le_normalizer_A1 : Th ≤ Subgroup.normalizer (A1 : Set Wc) :=
  fun w _ => Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => A1_normal.conj_mem x hx w, fun hx => by
      simpa [mul_assoc] using A1_normal.conj_mem _ hx w⁻¹⟩

theorem Jh_le_Th : Jh ≤ Th := baseSub_le_symSub (le_refl D) (le_refl D)

theorem Jh_le_normalizer_A1 : Jh ≤ Subgroup.normalizer (A1 : Set Wc) :=
  Th_le_normalizer_A1.trans' Jh_le_Th
theorem Jh_le_normalizer_A2 : Jh ≤ Subgroup.normalizer (A2 : Set Wc) :=
  Th_le_normalizer_A2.trans' Jh_le_Th
theorem Jh_le_normalizer_A3 : Jh ≤ Subgroup.normalizer (A3 : Set Wc) :=
  le_normalizer_of_forall (forall_mem_Jh fun a ha b hb => forall_mem_A3 fun c hc d hd => by
    revert a ha b hb c hc d hd; decide +kernel)
theorem Jh_le_normalizer_A4 : Jh ≤ Subgroup.normalizer (A4 : Set Wc) :=
  le_normalizer_of_forall (forall_mem_Jh fun a ha b hb => forall_mem_A4 fun c hc d hd => by
    revert a ha b hb c hc d hd; decide +kernel)

theorem normalizer_Jh : Subgroup.normalizer (Jh : Set Wc) = Th := by
  refine le_antisymm ?_ Th_le_normalizer_Jh
  intro w hw
  have h1 : w * ⟨r, 1, false⟩ * w⁻¹ ∈ Jh :=
    (Subgroup.mem_normalizer_iff.mp hw _).mp (by decide +kernel)
  have h2 : w * ⟨1, r, false⟩ * w⁻¹ ∈ Jh :=
    (Subgroup.mem_normalizer_iff.mp hw _).mp (by decide +kernel)
  have key : ∀ w : Wc, w * ⟨r, 1, false⟩ * w⁻¹ ∈ Jh → w * ⟨1, r, false⟩ * w⁻¹ ∈ Jh →
      w ∈ Th := by decide +kernel
  exact key w h1 h2

theorem centralizer_t0_Th : ∀ x ∈ Th, x * t0 = t0 * x → x ∈ Jh := by decide +kernel

theorem isPGroup_A1 : IsPGroup 2 A1 := IsPGroup.of_card (n := 4) (by rw [card_A1]; norm_num)

theorem pCore_Wc : CFSG.Open.pCore 2 Wc = A1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hN : (CFSG.Open.pCore 2 Wc).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hp : IsPGroup 2 (CFSG.Open.pCore 2 Wc) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hle : CFSG.Open.pCore 2 Wc ≤ Th := hp.le_sylow_of_normal thSylow
    have key : ∀ x ∈ Th, (⟨c3, 1, false⟩ : Wc) * x * (⟨c3, 1, false⟩ : Wc)⁻¹ ∈ Th →
        (⟨1, c3, false⟩ : Wc) * x * (⟨1, c3, false⟩ : Wc)⁻¹ ∈ Th → x ∈ A1 :=
      forall_mem_Th fun a ha b hb e => by revert a ha b hb e; decide +kernel
    intro x hx
    exact key x (hle hx) (hle (hN.conj_mem x hx _)) (hle (hN.conj_mem x hx _))
  · exact CFSG.LieType.BorelTits.le_pCore 2 A1_normal isPGroup_A1

theorem baseSub_inf (X Y X' Y' : Subgroup S4) :
    baseSub X Y ⊓ baseSub X' Y' = baseSub (X ⊓ X') (Y ⊓ Y') := by
  ext x
  simp only [Subgroup.mem_inf, mem_baseSub]
  tauto

theorem card_V_inf_V' : Nat.card ↥(V ⊓ V') = 2 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem card_A1_inf_A2 : Nat.card ↥(A1 ⊓ A2) = 4 := by
  rw [A1, A2, baseSub_inf, card_baseSub, card_V_inf_V']
theorem card_A3_inf_A4 : Nat.card ↥(A3 ⊓ A4) = 4 := by
  rw [A3, A4, baseSub_inf, card_baseSub, inf_comm V' V, card_V_inf_V']
theorem card_A1_inf_A3 : Nat.card ↥(A1 ⊓ A3) = 8 := by
  rw [A1, A3, baseSub_inf, card_baseSub, card_V_inf_V', inf_idem, card_V]
theorem card_A1_inf_A4 : Nat.card ↥(A1 ⊓ A4) = 8 := by
  rw [A1, A4, baseSub_inf, card_baseSub, inf_idem, card_V_inf_V', card_V]
theorem card_A2_inf_A3 : Nat.card ↥(A2 ⊓ A3) = 8 := by
  rw [A2, A3, baseSub_inf, card_baseSub, inf_idem, inf_comm V' V, card_V_inf_V', card_V']
theorem card_A2_inf_A4 : Nat.card ↥(A2 ⊓ A4) = 8 := by
  rw [A2, A4, baseSub_inf, card_baseSub, inf_comm V' V, card_V_inf_V', inf_idem, card_V']

@[expose] def Ai : Fin 4 → Subgroup Wc
  | 0 => A1
  | 1 => A2
  | 2 => A3
  | 3 => A4

@[expose] def interCard (i j : Fin 4) : ℕ :=
  match i.val, j.val with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => 16
  | 0, 1 | 1, 0 | 2, 3 | 3, 2 => 4
  | _, _ => 8

theorem card_Ai_inf (i j : Fin 4) : Nat.card ↥(Ai i ⊓ Ai j) = interCard i j := by
  fin_cases i <;> fin_cases j
  · show Nat.card ↥(A1 ⊓ A1) = 16; rw [inf_idem]; exact card_A1
  · exact card_A1_inf_A2
  · exact card_A1_inf_A3
  · exact card_A1_inf_A4
  · rw [inf_comm]; exact card_A1_inf_A2
  · show Nat.card ↥(A2 ⊓ A2) = 16; rw [inf_idem]; exact card_A2
  · exact card_A2_inf_A3
  · exact card_A2_inf_A4
  · rw [inf_comm]; exact card_A1_inf_A3
  · rw [inf_comm]; exact card_A2_inf_A3
  · show Nat.card ↥(A3 ⊓ A3) = 16; rw [inf_idem]; exact card_A3
  · exact card_A3_inf_A4
  · rw [inf_comm]; exact card_A1_inf_A4
  · rw [inf_comm]; exact card_A2_inf_A4
  · rw [inf_comm]; exact card_A3_inf_A4
  · show Nat.card ↥(A4 ⊓ A4) = 16; rw [inf_idem]; exact card_A4

theorem interCard_perm (σ : Fin 4 → Fin 4) (h : ∀ i j, interCard (σ i) (σ j) = interCard i j) :
    ∀ i, σ (σ (σ (σ i))) = i := by
  revert h
  revert σ
  decide +kernel

theorem s0_mem_Th : s0 ∈ Th := ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem Jh_eq_A1_sup_A2 : Jh = A1 ⊔ A2 := by
  apply le_antisymm
  · have hD : ∀ d ∈ dList, ∃ v ∈ vList, ∃ w ∈ v'List, v * w = d := by decide +kernel
    rintro ⟨a, b, e⟩ ⟨he, ha, hb⟩
    have he' : e = false := he
    subst he'
    obtain ⟨v₁, hv₁, w₁, hw₁, rfl⟩ := hD a ha
    obtain ⟨v₂, hv₂, w₂, hw₂, rfl⟩ := hD b hb
    have : (⟨v₁ * w₁, v₂ * w₂, false⟩ : Wc) = ⟨v₁, v₂, false⟩ * ⟨w₁, w₂, false⟩ := rfl
    rw [this]
    exact Subgroup.mul_mem_sup (show (⟨v₁, v₂, false⟩ : Wc) ∈ A1 from ⟨rfl, hv₁, hv₂⟩)
      (show (⟨w₁, w₂, false⟩ : Wc) ∈ A2 from ⟨rfl, hw₁, hw₂⟩)
  · exact sup_le (baseSub_le_baseSub V_le_D V_le_D) (baseSub_le_baseSub V'_le_D V'_le_D)

theorem z0_mem_Th : z0 ∈ Th := ⟨(by decide +kernel : tau ∈ D), (by decide +kernel : tau ∈ D)⟩

theorem z0_central : ∀ y ∈ Th, y * z0 = z0 * y :=
  forall_mem_Th fun a ha b hb e => by revert a ha b hb e; decide +kernel

theorem z0_sq : z0 * z0 = 1 := by decide +kernel

end CFSG.Quasithin.A10
