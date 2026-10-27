module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP
public import CFSG.Quasithin.Recognition.F112Crit.CoprimeCentralizer
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Delta
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5T

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_q1_commutator_mem_z1
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY2 : Q2 L1 L2 S ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) : Set G))
    (hYX : ∀ g ∈ L1 ⊔ S, ∀ y ∈ str83Y L1 L2 S, g * y * g⁻¹ * y⁻¹ ∈ str83X L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    {f : G} (hf : f ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G)) :
    ∀ u ∈ Q1 L1 L2 S, u * f * u⁻¹ * f⁻¹ ∈ Z1 L1 L2 S := by
  classical
  have hfr' := hfr
  obtain ⟨hF, hBS, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hBS ha hSz hL2 hZI
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  have hfY : f ∈ str83Y L1 L2 S := (Subgroup.mem_inf.mp hf).1
  have hXQ1 : X ≤ Q1 L1 L2 S := str83X_le_q1 hfr'
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr'
  have hQ1L : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  have hZ1X : Z1 L1 L2 S ≤ X := hZ1Z2.trans (z2_le_str83X L1 L2 S)
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    simpa using hX.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨y, hy⟩ : ↥X)
  have hcommXQ1 : ⁅X, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := str83G4_commutator_x_q1_le hfr'
  have hF2 : ∀ u ∈ Q1 L1 L2 S, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ Z1 L1 L2 S := by
    intro u hu x hx
    refine hcommXQ1 ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hx
  have hLP : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  have hQP : Q1 L1 L2 S ≤ P1 L1 L2 S := pCoreOf_le 2 (P1 L1 L2 S)
  have hNX : ∀ g ∈ P1 L1 L2 S, ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hg) x).mp hx
  have hNZ1 : ∀ g ∈ P1 L1 L2 S, ∀ z ∈ Z1 L1 L2 S, g * z * g⁻¹ ∈ Z1 L1 L2 S := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S) hg) z).mp hz
  have hNQ1 : ∀ g ∈ P1 L1 L2 S, ∀ u ∈ Q1 L1 L2 S, g * u * g⁻¹ ∈ Q1 L1 L2 S := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg) u).mp hu
  have hcancel : ∀ A B C : G, A * B = B * A → A⁻¹ * (B * A * C) = B * C := fun A B C h => by
    rw [← h]; group
  obtain ⟨c, hc⟩ : ∃ c : G → G, ∀ g, c g = g * f * g⁻¹ * f⁻¹ := ⟨_, fun _ => rfl⟩
  have hcX : ∀ g ∈ L1 ⊔ S, c g ∈ X := fun g hg => by rw [hc]; exact hYX g hg f hfY
  have hc1 : c 1 = 1 := by rw [hc]; group
  have hcoc : ∀ g h, c (g * h) = g * c h * g⁻¹ * c g := fun g h => by simp only [hc]; group
  have hhom : ∀ u ∈ Q1 L1 L2 S, ∀ v ∈ Q1 L1 L2 S,
      (c (u * v))⁻¹ * (c u * c v) ∈ Z1 L1 L2 S := by
    intro u hu v hv
    have ha := hcX u (hQ1L hu)
    have hb := hcX v (hQ1L hv)
    have ht : (u * c v * u⁻¹)⁻¹ ∈ X := X.inv_mem (hNX u (hQP hu) _ hb)
    have e : (c (u * v))⁻¹ * (c u * c v) = (c u)⁻¹ * ((u * c v * u⁻¹)⁻¹ * c u * c v) := by
      rw [hcoc u v]; group
    rw [e, hcancel _ _ _ (hXc _ ha _ ht),
      show (u * c v * u⁻¹)⁻¹ * c v = u * (c v)⁻¹ * u⁻¹ * (c v)⁻¹⁻¹ by group]
    exact hF2 u hu _ (X.inv_mem hb)
  have hequiv : ∀ g ∈ L1 ⊔ S, ∀ u ∈ Q1 L1 L2 S,
      (g * c u * g⁻¹)⁻¹ * c (g * u * g⁻¹) ∈ Z1 L1 L2 S := by
    intro g hg u hu
    have hu' : g * u * g⁻¹ ∈ Q1 L1 L2 S := hNQ1 g (hLP hg) u hu
    have hgX := hcX g hg
    have hA : g * c u * g⁻¹ ∈ X := hNX g (hLP hg) _ (hcX u (hQ1L hu))
    have hB' : g * u * g⁻¹ * (c g)⁻¹ * (g * u * g⁻¹)⁻¹ ∈ X :=
      hNX _ (hQP hu') _ (X.inv_mem hgX)
    have e : c (g * u * g⁻¹) =
        (g * u * g⁻¹ * (c g)⁻¹ * (g * u * g⁻¹)⁻¹) * (g * c u * g⁻¹) * c g := by
      simp only [hc]; group
    rw [e, hcancel _ _ _ (hXc _ hA _ hB')]
    have h := hF2 _ hu' _ (X.inv_mem hgX)
    rwa [inv_inv] at h
  let M : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∃ u ∈ Q1 L1 L2 S, x⁻¹ * c u ∈ Z1 L1 L2 S}
      mul_mem' := by
        rintro x₁ x₂ ⟨h₁X, u₁, hu₁, h₁⟩ ⟨h₂X, u₂, hu₂, h₂⟩
        refine ⟨X.mul_mem h₁X h₂X, u₁ * u₂, (Q1 L1 L2 S).mul_mem hu₁ hu₂, ?_⟩
        have hz : (x₁⁻¹ * c u₁) * c u₂ = c u₂ * (x₁⁻¹ * c u₁) :=
          hXc _ (hZ1X h₁) _ (hcX u₂ (hQ1L hu₂))
        have e : (x₁ * x₂)⁻¹ * c (u₁ * u₂) =
            (x₂⁻¹ * c u₂) * (x₁⁻¹ * c u₁) * ((c u₁ * c u₂)⁻¹ * c (u₁ * u₂)) := by
          calc (x₁ * x₂)⁻¹ * c (u₁ * u₂)
              = x₂⁻¹ * ((x₁⁻¹ * c u₁) * c u₂) * ((c u₁ * c u₂)⁻¹ * c (u₁ * u₂)) := by group
            _ = x₂⁻¹ * (c u₂ * (x₁⁻¹ * c u₁)) * ((c u₁ * c u₂)⁻¹ * c (u₁ * u₂)) := by rw [hz]
            _ = _ := by group
        rw [e]
        refine (Z1 L1 L2 S).mul_mem ((Z1 L1 L2 S).mul_mem h₂ h₁) ?_
        have h := (Z1 L1 L2 S).inv_mem (hhom u₁ hu₁ u₂ hu₂)
        rwa [show ((c (u₁ * u₂))⁻¹ * (c u₁ * c u₂))⁻¹ = (c u₁ * c u₂)⁻¹ * c (u₁ * u₂) by
          group] at h
      one_mem' := ⟨X.one_mem, 1, (Q1 L1 L2 S).one_mem, by
        rw [hc1, inv_one, one_mul]; exact (Z1 L1 L2 S).one_mem⟩
      inv_mem' := by
        rintro x ⟨hxX, u, hu, hxu⟩
        refine ⟨X.inv_mem hxX, u⁻¹, (Q1 L1 L2 S).inv_mem hu, ?_⟩
        have h1 : c u * c (u⁻¹) ∈ Z1 L1 L2 S := by
          have h := hhom u hu u⁻¹ ((Q1 L1 L2 S).inv_mem hu)
          rwa [mul_inv_cancel, hc1, inv_one, one_mul] at h
        have hz : x * (c u)⁻¹ = (c u)⁻¹ * x := hXc _ hxX _ (X.inv_mem (hcX u (hQ1L hu)))
        have e : x⁻¹⁻¹ * c (u⁻¹) = (x⁻¹ * c u)⁻¹ * (c u * c (u⁻¹)) := by
          calc x⁻¹⁻¹ * c (u⁻¹) = (x * (c u)⁻¹) * (c u * c (u⁻¹)) := by group
            _ = ((c u)⁻¹ * x) * (c u * c (u⁻¹)) := by rw [hz]
            _ = _ := by group
        rw [e]
        exact (Z1 L1 L2 S).mul_mem ((Z1 L1 L2 S).inv_mem hxu) h1 }
  have hmemM : ∀ x, x ∈ M ↔ x ∈ X ∧ ∃ u ∈ Q1 L1 L2 S, x⁻¹ * c u ∈ Z1 L1 L2 S :=
    fun _ => Iff.rfl
  have hMn : IsNormalIn (L1 ⊔ S) X M := by
    refine ⟨fun y hy => ((hmemM y).mp hy).1, fun g hg y hy => ?_⟩
    obtain ⟨hyX, u, hu, hyu⟩ := (hmemM y).mp hy
    refine (hmemM _).mpr ⟨hNX g (hLP hg) y hyX, g * u * g⁻¹, hNQ1 g (hLP hg) u hu, ?_⟩
    have e : (g * y * g⁻¹)⁻¹ * c (g * u * g⁻¹) =
        (g * (y⁻¹ * c u) * g⁻¹) * ((g * c u * g⁻¹)⁻¹ * c (g * u * g⁻¹)) := by group
    rw [e]
    exact (Z1 L1 L2 S).mul_mem (hNZ1 g (hLP hg) _ hyu) (hequiv g hg u hu)
  have hZ1M : Z1 L1 L2 S ≤ M := fun z hz => (hmemM z).mpr ⟨hZ1X hz, 1, (Q1 L1 L2 S).one_mem,
    by rw [hc1, mul_one]; exact (Z1 L1 L2 S).inv_mem hz⟩
  rcases hXstep.2.2.2 M hMn hZ1M (fun y hy => ((hmemM y).mp hy).1) with hMZ | hMX
  · intro u hu
    have h : c u ∈ M := (hmemM _).mpr ⟨hcX u (hQ1L hu), u, hu, by
      rw [inv_mul_cancel]; exact (Z1 L1 L2 S).one_mem⟩
    rw [hMZ, hc] at h
    exact h
  exfalso
  have hIX : X ⊓ Xw ≤ X := inf_le_left
  have hHZ2 : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hZ1Xw : Z1 L1 L2 S ≤ Xw := by
    intro z hz
    rw [hXwdef, CFSG.mem_conjugate_iff]
    exact z2_le_str83X L1 L2 S ((Subgroup.mem_normalizer_iff.mp (hHZ2 d.hwH2) z).mp (hZ1Z2 hz))
  have hZ1I : Z1 L1 L2 S ≤ X ⊓ Xw := le_inf hZ1X hZ1Xw
  haveI : ((X ⊓ Xw).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIX).mpr fun x hx =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun y hy => hXc y (hIX hy) x hx)
  let ψ : ↥(Q1 L1 L2 S) →* ↥X ⧸ (X ⊓ Xw).subgroupOf X :=
    MonoidHom.mk' (fun u => QuotientGroup.mk (s := (X ⊓ Xw).subgroupOf X)
      (⟨c u, hcX u (hQ1L u.2)⟩ : ↥X)) fun u v => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        exact hZ1I (hhom u u.2 v v.2)
  have hψ : ∀ u : ↥(Q1 L1 L2 S), ψ u = QuotientGroup.mk (s := (X ⊓ Xw).subgroupOf X)
      (⟨c u, hcX u (hQ1L u.2)⟩ : ↥X) := fun _ => rfl
  have hsurj : Function.Surjective ψ := by
    intro x'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x'
    have hxM : (x : G) ∈ M := by rw [hMX]; exact x.2
    obtain ⟨-, u, hu, hxu⟩ := (hmemM _).mp hxM
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hψ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (X ⊓ Xw).inv_mem (hZ1I hxu)
    rw [mul_inv_rev, inv_inv] at h
    exact h
  have hker : (Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q1 L1 L2 S) ≤ ψ.ker := by
    intro u hu
    obtain ⟨huQ1, huQ2⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hu)
    rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h1 : (u : G) * f * (u : G)⁻¹ ∈ str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hY2 huQ2) f).mp hf
    have h2 : c u ∈ str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) := by
      rw [hc]; exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hf)
    have h3 : c u ∈ X ⊓ Subgroup.centralizer (Xw : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcX u (hQ1L huQ1), (Subgroup.mem_inf.mp h2).2⟩
    rw [hXI] at h3
    exact h3
  obtain ⟨t, ht, htQ⟩ := SetLike.not_le_iff_exists.mp hB
  have hXwc : ∀ x ∈ Xw, ∀ y ∈ Xw, x * y = y * x := by
    intro x hx y hy
    rw [hXwdef, CFSG.mem_conjugate_iff] at hx hy
    have h := hXc _ hx _ hy
    have e1 : d.w * x * d.w⁻¹ * (d.w * y * d.w⁻¹) = d.w * (x * y) * d.w⁻¹ := by group
    have e2 : d.w * y * d.w⁻¹ * (d.w * x * d.w⁻¹) = d.w * (y * x) * d.w⁻¹ := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hIC : X ⊓ Xw ≤ X ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    refine le_inf inf_le_left fun y hy => Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact (Commute.zpow_left (hXwc t ht y (Subgroup.mem_inf.mp hy).2) k).eq
  have hq2 := (str83G4_cp_counts hfr' d hX ht htQ).2.1
  have hq : (Q2 L1 L2 S).relIndex S = 2 ^ (2 * a + 1) :=
    str86_relIndex_q2_s hF hBS (by omega) hL2
  have hidx1 : ψ.ker.index = (X ⊓ Xw).relIndex X := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    rfl
  have hidx2 : ψ.ker.index ≤ (Q2 L1 L2 S).relIndex S :=
    calc ψ.ker.index ≤ ((Q1 L1 L2 S ⊓ Q2 L1 L2 S).subgroupOf (Q1 L1 L2 S)).index :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
            (Subgroup.index_dvd_of_le hker)
      _ = (Q2 L1 L2 S).relIndex (Q1 L1 L2 S) := Subgroup.inf_relIndex_left _ _
      _ ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hQ1S (by rw [hq]; positivity)
  have hidx3 : (2 ^ (2 * a + 1)) ^ 2 ≤ (X ⊓ Xw).relIndex X := by
    rw [← hq2]
    exact Subgroup.relIndex_le_of_le_left hIC
      (by rw [← hidx1]; exact Subgroup.index_ne_zero_of_finite)
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hidx1, hq] at hidx2
  have h := hidx3.trans hidx2
  generalize 2 ^ (2 * a + 1) = q at h h8
  nlinarith

theorem str83G4_commutator_mem_z1_of_commute
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY2 : Q2 L1 L2 S ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) : Set G))
    (hYX : ∀ g ∈ L1 ⊔ S, ∀ y ∈ str83Y L1 L2 S, g * y * g⁻¹ * y⁻¹ ∈ str83X L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hD1I : ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1)
    {f : G} (hf : f ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G))
    (hfH : ∀ h ∈ d.D1 ⊔ d.D2, f * h = h * f) :
    ∀ g ∈ L1 ⊔ S, g * f * g⁻¹ * f⁻¹ ∈ Z1 L1 L2 S := by
  have hQ := str83G4_q1_commutator_mem_z1 hfr d hX hB hY2 hYX hXstep hXI hf
  obtain ⟨k, hkH, hkL1, hkfpf⟩ := str83G4_exists_fpf_x hfr d hXstep hIL2 hD1I
  have hfY : f ∈ str83Y L1 L2 S := (Subgroup.mem_inf.mp hf).1
  have hkf : k * f * k⁻¹ = f := by rw [← hfH k hkH, mul_inv_cancel_right]
  intro g hg
  have hu : k * g * k⁻¹ * g⁻¹ ∈ Q1 L1 L2 S :=
    str83G4_trivial_on_sup hfr (str83G4Data_sup_le_bigB d hkH) hkL1 g hg
  have hgX : g * f * g⁻¹ * f⁻¹ ∈ str83X L1 L2 S := hYX g hg f hfY
  refine hkfpf _ hgX ?_
  have h1 : k * (g * f * g⁻¹ * f⁻¹) * k⁻¹ =
      (k * g * k⁻¹ * g⁻¹) * (g * f * g⁻¹ * f⁻¹) * (k * g * k⁻¹ * g⁻¹)⁻¹ *
        ((k * g * k⁻¹ * g⁻¹) * f * (k * g * k⁻¹ * g⁻¹)⁻¹ * f⁻¹) := by
    calc k * (g * f * g⁻¹ * f⁻¹) * k⁻¹
        = k * g * k⁻¹ * (k * f * k⁻¹) * (k * g * k⁻¹)⁻¹ * (k * f * k⁻¹)⁻¹ := by group
      _ = k * g * k⁻¹ * f * (k * g * k⁻¹)⁻¹ * f⁻¹ := by rw [hkf]
      _ = _ := by group
  rw [h1]
  set u := k * g * k⁻¹ * g⁻¹ with hudef
  set cg := g * f * g⁻¹ * f⁻¹ with hcgdef
  have e : u * cg * u⁻¹ * (u * f * u⁻¹ * f⁻¹) * cg⁻¹ =
      (u * cg * u⁻¹ * cg⁻¹) * (cg * (u * f * u⁻¹ * f⁻¹) * cg⁻¹) := by group
  rw [e]
  refine (Z1 L1 L2 S).mul_mem ?_ ?_
  · refine str83G4_commutator_x_q1_le hfr ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hgX
  · exact (Subgroup.mem_normalizer_iff.mp
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
        (((str83X_le_q1 hfr).trans (pCoreOf_le 2 (P1 L1 L2 S))) hgX)) _).mp (hQ u hu)

theorem str83G4_eq_one_of_mem_y_inf_centralizer
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY2 : Q2 L1 L2 S ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) : Set G))
    (hYX : ∀ g ∈ L1 ⊔ S, ∀ y ∈ str83Y L1 L2 S, g * y * g⁻¹ * y⁻¹ ∈ str83X L1 L2 S)
    (hA : ∀ f ∈ str83Y L1 L2 S, (∀ g ∈ L1 ⊔ S, f ∈ Subgroup.centralizer
      (CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) g : Set G)) → f ∈ Z1 L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hD1I : ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1)
    {f : G} (hf : f ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G))
    (hfH : ∀ h ∈ d.D1 ⊔ d.D2, f * h = h * f) : f = 1 := by
  have hfr' := hfr
  have hc := str83G4_commutator_mem_z1_of_commute hfr d hX hB hY2 hYX hXstep hXI hIL2 hD1I hf hfH
  obtain ⟨hF, hBS, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hBS ha hSz hL2 hZI
  obtain ⟨hfY, hfC⟩ := Subgroup.mem_inf.mp hf
  have hXwS := str83G4_conjugate_x_le_s hfr' d hX
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hBS (Or.inl ⟨a, ha, hSz⟩)
  have hSZ1 : S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ L1 ⊔ S).trans (sup_eq_of_S_eq hS1).le).trans hZI
  have hfZ1 : f ∈ Z1 L1 L2 S := by
    refine hA f hfY fun g hg => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [SetLike.mem_coe, CFSG.mem_conjugate_iff] at hy
    have h1 : Commute (g * y * g⁻¹) (g * f * g⁻¹ * f⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hSZ1 (hXwS hy)) _ (hc g hg)).symm
    have h2 : Commute (g * y * g⁻¹) f := Subgroup.mem_centralizer_iff.mp hfC _ hy
    have h3 := h1.mul_right h2
    rw [show g * f * g⁻¹ * f⁻¹ * f = g * f * g⁻¹ by group] at h3
    have h4 : g * (y * f) * g⁻¹ = g * (f * y) * g⁻¹ := by
      calc g * (y * f) * g⁻¹ = (g * y * g⁻¹) * (g * f * g⁻¹) := by group
        _ = (g * f * g⁻¹) * (g * y * g⁻¹) := h3.eq
        _ = g * (f * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h4)
  obtain ⟨x, hx, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D1).resolve_left (str83G4Data_D1_ne_bot hfr' d)
  obtain ⟨δ, hδ, hxδ⟩ := str83G4_exists_delta_two hfr' d hx
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    exact hx1 (hδ₂ x hx fun l hl => by simpa using hxδ l hl)
  have hxδH : x * δ⁻¹ ∈ d.D1 ⊔ d.D2 :=
    (d.D1 ⊔ d.D2).mul_mem (Subgroup.mem_sup_left hx)
      ((d.D1 ⊔ d.D2).inv_mem (Subgroup.mem_sup_right hδ))
  refine str83G4_eq_one_of_fix_z2 hfr' d hZ2 hx hδ hδ1 hxδ (hZ1Z2 hfZ1) ?_
  rw [← hfH _ hxδH, mul_inv_cancel_right]

theorem str83G4_y_inf_centralizer_eq
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hY2 : Q2 L1 L2 S ≤ Subgroup.normalizer ((str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) : Subgroup G) : Set G))
    (hY5 : ∀ h ∈ d.D1 ⊔ d.D2, ∀ y ∈ str83Y L1 L2 S ⊓
      Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G),
      h * y * h⁻¹ * y⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hYX : ∀ g ∈ L1 ⊔ S, ∀ y ∈ str83Y L1 L2 S, g * y * g⁻¹ * y⁻¹ ∈ str83X L1 L2 S)
    (hA : ∀ f ∈ str83Y L1 L2 S, (∀ g ∈ L1 ⊔ S, f ∈ Subgroup.centralizer
      (CFSG.conjugate (CFSG.conjugate (str83X L1 L2 S) d.w) g : Set G)) → f ∈ Z1 L1 L2 S)
    (hXstep : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S))
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIL2 : ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S)
    (hD1I : ∀ x ∈ d.D1, (∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      x * y * x⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) → x = 1)
    (hZ2 : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hδ₂ : ∀ x ∈ d.D1, (∀ l ∈ L2, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) → x = 1) :
    str83Y L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  have hXQ1 : X ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    simpa using hX.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨y, hy⟩ : ↥X)
  have hXwc : ∀ x ∈ Xw, ∀ y ∈ Xw, x * y = y * x := by
    intro x hx y hy
    rw [hXwdef, CFSG.mem_conjugate_iff] at hx hy
    have h := hXc _ hx _ hy
    have e1 : d.w * x * d.w⁻¹ * (d.w * y * d.w⁻¹) = d.w * (x * y) * d.w⁻¹ := by group
    have e2 : d.w * y * d.w⁻¹ * (d.w * x * d.w⁻¹) = d.w * (y * x) * d.w⁻¹ := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hIY₀ : X ⊓ Xw ≤ str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) := fun y hy => by
    obtain ⟨hyX, hyXw⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hXQ1 hyX, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun z hz => hXc z hz y hyX
    · exact Subgroup.mem_centralizer_iff.mpr fun z hz => hXwc z hz y hyXw
  have hHP1 : d.D1 ⊔ d.D2 ≤ P1 L1 L2 S := (str83G4Data_sup_le_bigB d).trans le_sup_right
  obtain ⟨-, hHXw, -, -⟩ := str83G4_d1_sup_d2_le_normalizer hfr d
  have hHX : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer (X : Set G) :=
    hHP1.trans (le_normalizer_str83X L1 L2 S)
  have hHY₀ : d.D1 ⊔ d.D2 ≤
      Subgroup.normalizer ((str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) : Subgroup G) :
        Set G) := fun h hh =>
    A4.mem_normalizer_inf
      (A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hHP1 hh))
        (F7.normalizer_le_normalizer_centralizer _ (hHX hh)))
      (F7.normalizer_le_normalizer_centralizer _ (hHXw hh))
  have hHI : d.D1 ⊔ d.D2 ≤ Subgroup.normalizer ((X ⊓ Xw : Subgroup G) : Set G) := fun h hh =>
    A4.mem_normalizer_inf (hHX hh) (hHXw hh)
  have hY₀p : IsPGroup 2 ↥(str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G)) :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le
      ((inf_le_left : str83Y L1 L2 S ⊓ Subgroup.centralizer (Xw : Set G) ≤ str83Y L1 L2 S).trans
        inf_le_left)
  refine le_antisymm (fun f₀ hf₀ => ?_) hIY₀
  obtain ⟨n, hn, c, hc, hcH, rfl⟩ := F112Crit.exists_mul_centralizer_of_comm_mem hY₀p
    (str83G4Data_odd_card_sup d) hIY₀ hHY₀ hHI hf₀ fun h hh => by
      have h' := (X ⊓ Xw).inv_mem (hY5 h hh f₀ hf₀)
      rwa [show (h * f₀ * h⁻¹ * f₀⁻¹)⁻¹ = f₀ * h * f₀⁻¹ * h⁻¹ by group] at h'
  rw [str83G4_eq_one_of_mem_y_inf_centralizer hfr d hX hB hY2 hYX hA hXstep hXI hIL2 hD1I hZ2
    hδ₂ hc hcH, mul_one]
  exact hn

end CFSG.Quasithin.Stroth

end
