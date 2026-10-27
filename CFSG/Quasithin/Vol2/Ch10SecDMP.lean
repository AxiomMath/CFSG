module

public import CFSG.Quasithin.Vol2.Ch10SecD211A
public import CFSG.Quasithin.Vol2.Ch10SecD211F
public import CFSG.Quasithin.Vol2.Ch10SecDXI2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
theorem L3.exists_fix_map : ∀ c : CFSG.Quasithin.L3.Vec, c ≠ 0 →
    ∀ d e : CFSG.Quasithin.L3.Vec, d ≠ 0 → e ≠ 0 → d ≠ c → e ≠ c →
      ∃ σ : CFSG.Quasithin.L3.Γ, CFSG.Quasithin.L3.act σ c = c ∧
        CFSG.Quasithin.L3.act σ d = e := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
theorem L3.exists_fix_move : ∀ c w : CFSG.Quasithin.L3.Vec, c ≠ 0 → w ≠ 0 → w ≠ c →
    ∃ σ : CFSG.Quasithin.L3.Γ, CFSG.Quasithin.L3.act σ c = c ∧
      CFSG.Quasithin.L3.act σ w ≠ w := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem mul_comm_of_conj_eq {x v : G} (h : x * v * x⁻¹ = v) : x * v = v * x := by
  calc x * v = x * v * x⁻¹ * x := by group
    _ = v * x := by rw [h]

theorem mem_P_of_mem_L (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) {a : G} (ha : a ∈ L)
    (hav : a * v₁ = v₁ * a) :
    a ∈ (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
  obtain ⟨ht, htn, -, -, hv2, -⟩ := hd
  have hav2 : a * v₂ = v₂ * a :=
    (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hv2.1)) a ha
  refine ⟨Subgroup.mem_sup_left (SecA.le_fsuL0 T L ha),
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← mul_assoc, hav, mul_assoc, hav2, mul_assoc]

omit [Finite G] in
theorem coord_conj [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥) {b : G}
    (hbN : b ∈ Subgroup.normalizer (fsuUL T L I : Set G)) {σ : L3.Γ}
    (hb : conjAct (fsuUL T L I) ⟨b, hbN⟩ = D.rho σ) {u : G} (hu : u ∈ fsuUL T L I)
    (hbu : b * u * b⁻¹ ∈ fsuUL T L I) :
    coord D ⟨b * u * b⁻¹, hbu⟩ = L3.act σ (coord D ⟨u, hu⟩) := by
  rw [← coord_rho, ← hb]
  rfl

omit [Finite G] in
theorem exists_mem_L_rho [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥) (σ : L3.Γ) :
    ∃ b ∈ L, ∃ hbN : b ∈ Subgroup.normalizer (fsuUL T L I : Set G),
      conjAct (fsuUL T L I) ⟨b, hbN⟩ = D.rho σ := by
  obtain ⟨⟨b, hbN⟩, hbL, hb⟩ := D.rho_mem σ
  exact ⟨b, Subgroup.mem_subgroupOf.mp hbL, hbN, hb⟩

omit [Finite G] in
theorem coord_ne [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥) {u w : G}
    (hu : u ∈ fsuUL T L I) (hw : w ∈ fsuUL T L I) (huw : u ≠ w) :
    coord D ⟨u, hu⟩ ≠ coord D ⟨w, hw⟩ := fun h1 =>
  huw (congrArg Subtype.val (coord_injective D h1))

omit [Finite G] in
theorem coord_one' [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥) :
    coord D ⟨1, (fsuUL T L I).one_mem⟩ = 0 :=
  coord_one D

omit [Finite G] in
theorem exists_mem_L_ne (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {v₁ : G}
    (hv1 : v₁ ∈ fsuUL T L I) (hv11 : v₁ ≠ 1) : ∃ a ∈ L, a * v₁ * a⁻¹ ≠ v₁ := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hc0 : coord D ⟨v₁, hv1⟩ ≠ 0 := by
    rw [← coord_one' D]
    exact coord_ne D hv1 _ hv11
  obtain ⟨σ, hσ⟩ := CFSG.Quasithin.L3.act_nofix _ hc0
  obtain ⟨a, haL, haN, ha⟩ := exists_mem_L_rho D σ
  have hav : a * v₁ * a⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp haN v₁).mp hv1
  refine ⟨a, haL, fun h1 => hσ ?_⟩
  rw [← coord_conj D haN ha hv1 hav]
  congr 1
  exact Subtype.ext h1

theorem exists_conj_ne (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {K : Subgroup G}
    (hPK : (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) ≤ K) {l : G}
    (hlK : l ∈ K) (hlL0 : l ∈ fsuL0 T L) (hlv : l * v₁ * l⁻¹ ≠ v₁) :
    ∃ g ∈ K, g ∈ L ∧ g * v₁ * g⁻¹ ≠ v₁ := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hd' := hd
  obtain ⟨ht, htn, hv1, hv11, -, -⟩ := hd'
  obtain ⟨hN1, -⟩ := fsuL0_le_normalizer_V12 h37 h38 h ht htn
  have hw : l⁻¹ * v₁ * l ∈ fsuUL T L I := by
    have := (Subgroup.mem_normalizer_iff.mp (hN1 ((fsuL0 T L).inv_mem hlL0)) v₁).mp hv1.1
    simpa using this
  have hw1 : l⁻¹ * v₁ * l ≠ 1 := fun h1 => hv11 (by
    calc v₁ = l * (l⁻¹ * v₁ * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hwv : l⁻¹ * v₁ * l ≠ v₁ := fun h1 => hlv (by
    calc l * v₁ * l⁻¹ = l * (l⁻¹ * v₁ * l) * l⁻¹ := by rw [h1]
      _ = v₁ := by group)
  have hc0 : coord D ⟨v₁, hv1.1⟩ ≠ 0 := by
    rw [← coord_one' D]
    exact coord_ne D hv1.1 _ hv11
  obtain ⟨σ, hσc, hσw⟩ := L3.exists_fix_move _ _ hc0
    (by rw [← coord_one' D]; exact coord_ne D hw _ hw1) (coord_ne D hw hv1.1 hwv)
  obtain ⟨c, hcL, hcN, hcσ⟩ := exists_mem_L_rho D σ
  have hcv1 : c * v₁ * c⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp hcN v₁).mp hv1.1
  have hcv : c * v₁ * c⁻¹ = v₁ := congrArg Subtype.val (coord_injective D
    (show coord D ⟨_, hcv1⟩ = coord D ⟨v₁, hv1.1⟩ by rw [coord_conj D hcN hcσ hv1.1 hcv1, hσc]))
  have hcK : c ∈ K := hPK (mem_P_of_mem_L h37 h38 h hd hcL (mul_comm_of_conj_eq hcv))
  have hLN := (fsuL0_le_normalizer_L h37 h38 h ht htn).1
  refine ⟨l * c * l⁻¹, K.mul_mem (K.mul_mem hlK hcK) (K.inv_mem hlK),
    (Subgroup.mem_normalizer_iff.mp (hLN hlL0) c).mp hcL, fun h1 => hσw ?_⟩
  have hcw : c * (l⁻¹ * v₁ * l) * c⁻¹ ∈ fsuUL T L I :=
    (Subgroup.mem_normalizer_iff.mp hcN _).mp hw
  rw [← coord_conj D hcN hcσ hw hcw]
  congr 1
  apply Subtype.ext
  calc c * (l⁻¹ * v₁ * l) * c⁻¹ = l⁻¹ * (l * c * l⁻¹ * v₁ * (l * c * l⁻¹)⁻¹) * l := by group
    _ = l⁻¹ * v₁ * l := by rw [h1]

theorem L_le_of_mem_ne (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {K : Subgroup G}
    (hPK : (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) ≤ K) {g : G}
    (hgK : g ∈ K) (hgL : g ∈ L) (hgv : g * v₁ * g⁻¹ ≠ v₁) : L ≤ K := by
  obtain ⟨_, ⟨D⟩⟩ := nonempty_l3Data h3 hc
  have hv1 : v₁ ∈ fsuUL T L I := hd.2.2.1.1
  have hv11 : v₁ ≠ 1 := hd.2.2.2.1
  have hc0 : coord D ⟨v₁, hv1⟩ ≠ 0 := by
    rw [← coord_one' D]
    exact coord_ne D hv1 _ hv11
  have hconj1 : ∀ x ∈ L, x * v₁ * x⁻¹ ∈ fsuUL T L I := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_V1 hx) v₁).mp hv1
  have hne1 : ∀ x ∈ L, x * v₁ * x⁻¹ ≠ 1 := fun x _ h1 => hv11 (by
    calc v₁ = x⁻¹ * (x * v₁ * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  intro a haL
  by_cases hav : a * v₁ * a⁻¹ = v₁
  · exact hPK (mem_P_of_mem_L h37 h38 h hd haL (mul_comm_of_conj_eq hav))
  obtain ⟨σ, hσc, hσe⟩ := L3.exists_fix_map _ hc0 _ _
    (by rw [← coord_one' D]; exact coord_ne D (hconj1 g hgL) _ (hne1 g hgL))
    (by rw [← coord_one' D]; exact coord_ne D (hconj1 a haL) _ (hne1 a haL))
    (coord_ne D (hconj1 g hgL) hv1 hgv) (coord_ne D (hconj1 a haL) hv1 hav)
  obtain ⟨b, hbL, hbN, hbσ⟩ := exists_mem_L_rho D σ
  have hbv : b * v₁ * b⁻¹ = v₁ := congrArg Subtype.val (coord_injective D
    (show coord D ⟨_, hconj1 b hbL⟩ = coord D ⟨v₁, hv1⟩ by
      rw [coord_conj D hbN hbσ hv1 (hconj1 b hbL), hσc]))
  have hbg : b * (g * v₁ * g⁻¹) * b⁻¹ = a * v₁ * a⁻¹ := by
    have hmem : b * (g * v₁ * g⁻¹) * b⁻¹ ∈ fsuUL T L I :=
      (Subgroup.mem_normalizer_iff.mp hbN _).mp (hconj1 g hgL)
    exact congrArg Subtype.val (coord_injective D (show coord D ⟨_, hmem⟩ =
      coord D ⟨_, hconj1 a haL⟩ by rw [coord_conj D hbN hbσ (hconj1 g hgL) hmem, hσe]))
  have hfix : ((b * g)⁻¹ * a) * v₁ * ((b * g)⁻¹ * a)⁻¹ = v₁ := by
    calc ((b * g)⁻¹ * a) * v₁ * ((b * g)⁻¹ * a)⁻¹ = (b * g)⁻¹ * (a * v₁ * a⁻¹) * (b * g) := by
          group
      _ = (b * g)⁻¹ * (b * (g * v₁ * g⁻¹) * b⁻¹) * (b * g) := by rw [hbg]
      _ = v₁ := by group
  have hm := hPK (mem_P_of_mem_L h37 h38 h hd (L.mul_mem (L.inv_mem (L.mul_mem hbL hgL)) haL)
    (mul_comm_of_conj_eq hfix))
  have hbK := hPK (mem_P_of_mem_L h37 h38 h hd hbL (mul_comm_of_conj_eq hbv))
  rw [show a = b * g * ((b * g)⁻¹ * a) by group]
  exact K.mul_mem (K.mul_mem hbK hgK) hm

end CFSG.Quasithin.Vol2.Ch10.SecD
