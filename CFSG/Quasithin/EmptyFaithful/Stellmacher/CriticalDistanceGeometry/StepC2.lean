module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S5Overgroup

public section

namespace CFSG.Quasithin
open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace F53
open Equiv
open scoped Pointwise

theorem T0fin_cent : ∀ x ∈ D0fin, (∀ r ∈ T0fin, x * r = r * x) → x ∈ T0fin := by
  decide +kernel
theorem That0fin_cent : ∀ x ∈ D0fin, (∀ r ∈ That0fin, x * r = r * x) → x ∈ That0fin := by
  decide +kernel

theorem klein_fin1 : ∀ F ∈ D0fin.powerset, (∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) → (∀ x ∈ F, x * x = 1) →
    F.card ≤ 4 := by
  decide +kernel

theorem exists_conj_D0 (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    ∃ g : Perm (Fin 5), ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ D0fin := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, -⟩ := sylow_of_card_eight D0 D0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) (hP2.toSylow hPs)
  refine ⟨g, fun x => ?_⟩
  have h1 : P = MulAut.conj g • D0 := by
    have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : y ∈ D0fin := hy
    have e : g⁻¹ * (MulAut.conj g • y) * g = y := by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [e]; exact this
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.conj_apply]; group

theorem card_le_four_and_cent (P R : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) (hRP : R ≤ P)
    (hR2 : ∀ r ∈ R, r * r = 1) :
    Nat.card R ≤ 4 ∧ (Nat.card R = 4 → ∀ x ∈ P, (∀ r ∈ R, x * r = r * x) → x ∈ R) := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_D0 P hP
  set φ : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  have hφ' : ∀ x, φ x = g⁻¹ * x * g := by intro x; simp [φ]
  set R' := R.map φ with hR'
  have hR'D : R' ≤ D0 := by
    rintro _ ⟨r, hr, rfl⟩
    show φ r ∈ D0fin
    rw [hφ']; exact (hg r).mp (hRP hr)
  have hcard : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective hφinj
  set F := D0fin.filter (fun x => x ∈ R') with hF
  have hmem : ∀ x, x ∈ F ↔ x ∈ R' := by
    intro x
    simp only [hF, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hR'D h, h⟩⟩
  have hFc : F.card = Nat.card R := by
    rw [← hcard]
    have : (R' : Set (Perm (Fin 5))) = ↑F := by ext x; simp [hmem]
    show F.card = Nat.card (R' : Set (Perm (Fin 5)))
    rw [this]; simp
  have hFmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F :=
    fun x hx y hy => (hmem _).mpr (R'.mul_mem ((hmem _).mp hx) ((hmem _).mp hy))
  have hFsq : ∀ x ∈ F, x * x = 1 := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (hmem x).mp hx
    have h1 := hR2 r hr
    rw [← hrx, ← map_mul, h1, map_one]
  have hFsub : F ∈ D0fin.powerset := by simp [hF]
  refine ⟨?_, fun h4 x hx hxc => ?_⟩
  · rw [← hFc]; exact klein_fin1 F hFsub hFmul hFsq
  · have hF4 : F.card = 4 := by rw [hFc]; exact h4
    have hcl := klein_classify F hFsub hF4 hFmul hFsq
    have hxD : g⁻¹ * x * g ∈ D0fin := (hg x).mp hx
    have hxF : g⁻¹ * x * g ∈ F := by
      have hc : ∀ r ∈ F, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
        intro r hr
        obtain ⟨r0, hr0, rfl⟩ := (hmem r).mp hr
        rw [hφ']
        have := hxc r0 hr0
        calc g⁻¹ * x * g * (g⁻¹ * r0 * g) = g⁻¹ * (x * r0) * g := by group
          _ = g⁻¹ * (r0 * x) * g := by rw [this]
          _ = _ := by group
      rcases hcl with h | h
      · rw [h] at hc ⊢; exact T0fin_cent _ hxD hc
      · rw [h] at hc ⊢; exact That0fin_cent _ hxD hc
    obtain ⟨r, hr, hrx⟩ := (hmem _).mp hxF
    rw [hφ'] at hrx
    have : r = x := by
      have h2 := congrArg (fun y => g * y * g⁻¹) hrx
      simpa [mul_assoc] using h2
    rwa [← this]


end F53

namespace F53.Stellmacher

open CosetGeom Equiv F53
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem edge_decomp (hA : F53Amalgam H M S) {α δ δ' : Geo H M} (hδ : δ ∈ nbrs α)
    (hδ' : δ' ∈ nbrs α) (hS : Qv δ ⊔ Qv α = stab α ⊓ stab δ) (hZ : Zv δ' ≤ stab δ) :
    ∀ u ∈ stab α ⊓ stab δ, ∀ z ∈ Zv δ', ∃ z' ∈ Zv δ', ∃ q ∈ Qv δ, u * z * u⁻¹ = z' * q := by
  intro u hu z hz
  have hN : Qv α ≤ Subgroup.normalizer (Qv δ : Set G) :=
    (Qv_le_stab_of_mem_nbrs hA hδ).trans (le_normalizer_pCoreOf 2 (stab δ))
  rw [← hS, sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hu
  obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hu
  have hz1 : b * z * b⁻¹ ∈ Zv δ' :=
    (Subgroup.mem_normalizer_iff.mp
      (stab_le_normalizer_Zv hA δ' (Qv_le_stab_of_mem_nbrs hA hδ' hb)) z).mp hz
  have hzs : z ∈ stab δ := hZ hz
  have hq1 : z⁻¹ * a * z⁻¹⁻¹ ∈ Qv δ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab δ) ((stab δ).inv_mem hzs)) a).mp ha
  have hq1' : z⁻¹ * a * z * a⁻¹ ∈ Qv δ := by
    have := (Qv δ).mul_mem hq1 ((Qv δ).inv_mem ha)
    simpa [mul_assoc] using this
  have hq2 : b * (z⁻¹ * a * z * a⁻¹) * b⁻¹ ∈ Qv δ :=
    (Subgroup.mem_normalizer_iff.mp (hN hb) _).mp hq1'
  exact ⟨b * z * b⁻¹, hz1, _, hq2, by group⟩

theorem edge_image (hA : F53Amalgam H M S) {α δ δ' : Geo H M} (hδ : δ ∈ nbrs α)
    (hδ' : δ' ∈ nbrs α) (hvδ : vtype δ = false) (hS : Qv δ ⊔ Qv α = stab α ⊓ stab δ)
    (hZ : Zv δ' ≤ Qv α) :
    ∃ ψ : ↥(stab δ) →* Perm (Fin 5), Function.Surjective ψ ∧
      (∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ) ∧
      Nat.card (((stab δ ⊓ stab α).subgroupOf (stab δ)).map ψ) = 8 ∧
      Nat.card (((Zv δ').subgroupOf (stab δ)).map ψ) = (Zv δ' ⊓ Qv δ).relIndex (Zv δ') ∧
      ((Zv δ').subgroupOf (stab δ)).map ψ ≤ ((stab δ ⊓ stab α).subgroupOf (stab δ)).map ψ ∧
      (∀ p ∈ ((stab δ ⊓ stab α).subgroupOf (stab δ)).map ψ, ∀ z ∈ ((Zv δ').subgroupOf (stab δ)).map ψ,
        p * z * p⁻¹ ∈ ((Zv δ').subgroupOf (stab δ)).map ψ) ∧
      (∀ z ∈ ((Zv δ').subgroupOf (stab δ)).map ψ, z * z = 1) := by
  have hαδ : α ∈ nbrs δ := (show (graph (H ⊔ M) H M).Adj α δ from hδ).symm
  have hZδ : Zv δ' ≤ stab δ := hZ.trans (Qv_le_stab_of_mem_nbrs hA hδ)
  have hZα : Zv δ' ≤ stab α := hZ.trans (pCoreOf_le 2 _)
  obtain ⟨n, ψ, hn, hsurj, hker⟩ := exists_quotHom hA δ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
  swap
  · simp [hvδ] at hv
  refine ⟨ψ, hsurj, hker, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_map_subgroupOf_eq ψ hker inf_le_left, relIndex_Qv_inf_false hA hαδ hvδ]
  · rw [card_map_subgroupOf_eq ψ hker hZδ, ← Subgroup.inf_relIndex_left, inf_comm]
  · refine Subgroup.map_mono fun x hx => ?_
    exact ⟨x.2, hZα hx⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    have hu' : (u : G) ∈ stab δ ⊓ stab α := hu
    obtain ⟨z', hz', q, hq, heq⟩ := edge_decomp hA hδ hδ' hS hZδ (u : G) ⟨hu'.2, hu'.1⟩ (w : G) hw
    have hz's : z' ∈ stab δ := hZδ hz'
    have hqs : q ∈ stab δ := pCoreOf_le 2 _ hq
    have key : u * w * u⁻¹ = (⟨z', hz's⟩ : ↥(stab δ)) * ⟨q, hqs⟩ := Subtype.ext (by simpa using heq)
    refine ⟨⟨z', hz's⟩, hz', ?_⟩
    have : ψ ⟨q, hqs⟩ = 1 := (hker _).mpr hq
    calc ψ ⟨z', hz's⟩ = ψ ⟨z', hz's⟩ * ψ ⟨q, hqs⟩ := by rw [this, mul_one]
      _ = ψ (u * w * u⁻¹) := by rw [key, map_mul]
      _ = _ := by simp
  · rintro _ ⟨w, hw, rfl⟩
    have hw2 : (w : G) * w = 1 := by
      have := (isElemAbelian_Zv hA δ').2 (w : G) hw
      simpa [pow_two] using this
    rw [← map_mul]
    have : w * w = 1 := Subtype.ext (by simpa using hw2)
    rw [this, map_one]

theorem zbar_card_four (hA : F53Amalgam H M S) (h113a : Hss113aAt H M) (hM6 : NoA5Transvection)
    (hb2 : bMin H M = 2) {α β γ : Geo H M} (hvα : vtype α = true) (hβ : β ∈ nbrs α)
    (hγ : γ ∈ nbrs α) (hβγ : β ≠ γ) (hbβ : bAt β = 2) (hbγ : bAt γ = 2)
    (hSβ : Qv β ⊔ Qv α = stab α ⊓ stab β) (hZγ : ¬ Zv γ ≤ Qv β) (hZγα : Zv γ ≤ Qv α)
    (hZβα : Zv β ≤ Qv α) :
    (Zv γ ⊓ Qv β).relIndex (Zv γ) = 4 ∧ (Zv β ⊓ Qv γ).relIndex (Zv β) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvβ : vtype β = false := by
    have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj α β from hβ)
    revert this; cases hvβ : vtype β <;> simp [hvα]
  have hZγβ : Zv γ ≤ stab β := hZγα.trans (Qv_le_stab_of_mem_nbrs hA hβ)
  have hZβγ : Zv β ≤ stab γ := hZβα.trans (Qv_le_stab_of_mem_nbrs hA hγ)
  have hbβ' : bAt β = bMin H M := by rw [hbβ, hb2]
  have hbγ' : bAt γ = bMin H M := by rw [hbγ, hb2]
  have hdist : dist γ β = bMin H M := by
    have h1 : dist γ β ≤ 2 := by
      have := dist_triangle_of_adj (show (graph (H ⊔ M) H M).Adj γ α from
        (show (graph (H ⊔ M) H M).Adj α γ from hγ).symm) β
      have h2 : dist γ α = 1 := dist_eq_one_iff_adj.mpr
        (show (graph (H ⊔ M) H M).Adj α γ from hγ).symm
      have h3 : dist α β = 1 := dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj α β from hβ)
      omega
    have h0 : dist γ β ≠ 0 := fun h => hβγ ((dist_eq_zero_iff hA.amalgam.gen).mp h).symm
    have h1' : dist γ β ≠ 1 := fun h => hZγ (Zv_le_Qv_of_dist_lt (by omega))
    omega
  have hcomm : ⁅Zv γ, Zv β⁆ ≠ ⊥ := by
    intro h
    apply hZγ
    have hcβ : stab β ⊓ Subgroup.centralizer (Zv β : Set G) = Qv β :=
      centralizer_Zv_eq_Qv_of_bAt hA hbβ'
    rw [← hcβ]
    exact le_inf hZγβ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have h113 := h113a γ β ⟨hZγ, hdist⟩ hcomm
  obtain ⟨ψ, hsurjβ, hkβ, hPcard, hZcard, hZbP, hnormZ, hsq⟩ := edge_image hA hβ hγ hvβ hSβ hZγα
  set Zb : Subgroup (Perm (Fin 5)) := ((Zv γ).subgroupOf (stab β)).map ψ with hZb
  set Pb : Subgroup (Perm (Fin 5)) := ((stab β ⊓ stab α).subgroupOf (stab β)).map ψ with hPb
  have ha1 : (Zv γ ⊓ Qv β).relIndex (Zv γ) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro h; exact hZγ (h.trans inf_le_right)
  obtain ⟨hle4, -⟩ := card_le_four_and_cent Pb Zb hPcard hZbP hsq
  have hdvd : Nat.card Zb ∣ 8 := hPcard ▸ Subgroup.card_dvd_of_le hZbP
  have hpos : 0 < Nat.card Zb := Nat.card_pos
  have ha : (Zv γ ⊓ Qv β).relIndex (Zv γ) = 4 := by
    rw [← hZcard] at ha1 ⊢
    have key : ∀ a : ℕ, a ∣ 8 → a ≤ 4 → a ≠ 1 → 0 < a → a = 2 ∨ a = 4 := by
      intro a h1 h2 h3 h4
      interval_cases a <;> simp_all
    rcases key _ hdvd hle4 ha1 hpos with h2 | h4
    · exfalso
      have hZbcard : Nat.card Zb = 2 := h2
      obtain ⟨z, hzmem, hz1, huniq⟩ : ∃ z ∈ Zb, z ≠ 1 ∧ ∀ y ∈ Zb, y ≠ 1 → y = z := by
        obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : Zb)).mp hZbcard
        refine ⟨z, z.2, fun h => hz (Subtype.ext h), fun y hy hy1 => ?_⟩
        have := huniq ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
        exact congrArg Subtype.val this
      obtain ⟨⟨s, hsβ⟩, hsZ, hψs⟩ := hzmem
      have hsZ' : s ∈ Zv γ := hsZ
      have hcentral : ∀ p ∈ Pb, p * z = z * p := by
        intro p hp
        have h1 : p * z * p⁻¹ ∈ Zb := hnormZ p hp z ⟨⟨s, hsβ⟩, hsZ, hψs⟩
        have h2 : p * z * p⁻¹ ≠ 1 := by
          intro h
          apply hz1
          calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
            _ = 1 := by rw [h]; simp
        have := huniq _ h1 h2
        calc p * z = (p * z * p⁻¹) * p := by group
          _ = z * p := by rw [this]
      have hzalt : z ∈ alternatingGroup (Fin 5) :=
        sign_eq_one_of_central_card_eight Pb hPcard z (hZbP ⟨_, hsZ, hψs⟩)
          (fun y hy => hcentral y hy)
      have hs2 : (s : G) ^ 2 = 1 := (isElemAbelian_Zv hA γ).2 s hsZ'
      have hz2 : z ^ 2 = 1 := by
        rw [← hψs, ← map_pow]
        have : (⟨s, hsβ⟩ : ↥(stab β)) ^ 2 = 1 := Subtype.ext (by simpa using hs2)
        rw [this, map_one]
      have hcγ : stab γ ⊓ Subgroup.centralizer (Zv γ : Set G) = Qv γ :=
        centralizer_Zv_eq_Qv_of_bAt hA hbγ'
      have hcβ : stab β ⊓ Subgroup.centralizer (Zv β : Set G) = pCoreOf 2 (stab β) :=
        centralizer_Zv_eq_Qv_of_bAt hA hbβ'
      have hs1 : ψ ⟨s, hsβ⟩ ≠ 1 := by rw [hψs]; exact hz1
      have hceq : Zv β ⊓ Subgroup.centralizer ({s} : Set G) = Zv β ⊓ Qv γ := by
        ext x
        constructor
        · rintro ⟨hxZ, hxs⟩
          refine ⟨hxZ, ?_⟩
          rw [← hcγ]
          refine ⟨hZβγ hxZ, ?_⟩
          refine Subgroup.mem_centralizer_iff.mpr ?_
          intro w hw
          have hxQ : ∀ q ∈ Qv β, q * x = x * q :=
            Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hxZ).2
          have hxs' : s * x = x * s := Subgroup.mem_centralizer_iff.mp hxs s rfl
          have hwβ : w ∈ stab β := hZγβ hw
          have hwZ : ψ ⟨w, hwβ⟩ ∈ Zb := ⟨_, hw, rfl⟩
          by_cases hw1 : ψ ⟨w, hwβ⟩ = 1
          · exact hxQ w ((hkβ _).mp hw1)
          · have heq : ψ ⟨w, hwβ⟩ = ψ ⟨s, hsβ⟩ := by rw [hψs]; exact huniq _ hwZ hw1
            have hq : s⁻¹ * w ∈ Qv β := by
              rw [← hkβ ⟨s⁻¹ * w, (stab β).mul_mem ((stab β).inv_mem hsβ) hwβ⟩]
              have : (⟨s⁻¹ * w, (stab β).mul_mem ((stab β).inv_mem hsβ) hwβ⟩ : ↥(stab β)) =
                  ⟨s, hsβ⟩⁻¹ * ⟨w, hwβ⟩ := rfl
              rw [this, map_mul, map_inv, heq, inv_mul_cancel]
            have hq' := hxQ _ hq
            calc w * x = s * ((s⁻¹ * w) * x) := by group
              _ = s * (x * (s⁻¹ * w)) := by rw [hq']
              _ = (s * x) * (s⁻¹ * w) := by group
              _ = (x * s) * (s⁻¹ * w) := by rw [hxs']
              _ = x * w := by group
        · rintro ⟨hxZ, hxQ⟩
          refine ⟨hxZ, ?_⟩
          refine Subgroup.mem_centralizer_iff.mpr ?_
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA γ hsZ').2 x hxQ).symm
      refine hM6 G (stab β) (Zv β) ψ hsurjβ hkβ (Zv_le_Qv hA β)
        (stab_le_normalizer_Zv hA β) (isElemAbelian_Zv hA β) hcβ s hsβ hs1
        (by rw [hψs]; exact hz2) (by rw [hψs]; exact hzalt) ?_
      rw [hceq, ← h113, ← hZcard, h2]
    · exact h4
  exact ⟨ha, by rw [← h113, ha]⟩

theorem comm_N_Zgamma_le (hA : F53Amalgam H M S) (h113a : Hss113aAt H M) (hM6 : NoA5Transvection)
    (hb2 : bMin H M = 2) {α β γ : Geo H M} (hvα : vtype α = true) (hβ : β ∈ nbrs α)
    (hγ : γ ∈ nbrs α) (hβγ : β ≠ γ) (hbβ : bAt β = 2) (hbγ : bAt γ = 2)
    (hSβ : Qv β ⊔ Qv α = stab α ⊓ stab β) (hSγ : Qv γ ⊔ Qv α = stab α ⊓ stab γ)
    (hZγ : ¬ Zv γ ≤ Qv β) (hZγα : Zv γ ≤ Qv α) (hZβα : Zv β ≤ Qv α) :
    ⁅Qv α ⊓ Qv β, Zv γ⁆ ≤ Zv β := by
  have hvγ : vtype γ = false := by
    have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj α γ from hγ)
    revert this; cases hvγ : vtype γ <;> simp [hvα]
  have hZγβ : Zv γ ≤ stab β := hZγα.trans (Qv_le_stab_of_mem_nbrs hA hβ)
  have hZβγ : Zv β ≤ stab γ := hZβα.trans (Qv_le_stab_of_mem_nbrs hA hγ)
  have hcard4 := (zbar_card_four hA h113a hM6 hb2 hvα hβ hγ hβγ hbβ hbγ hSβ hZγ hZγα hZβα).2
  obtain ⟨ψ, hsurj, hker, hPcard, hZcard, hZbP, hnormZ, hsq⟩ := edge_image hA hγ hβ hvγ hSγ hZβα
  set Zb : Subgroup (Perm (Fin 5)) := ((Zv β).subgroupOf (stab γ)).map ψ with hZb
  set Pb : Subgroup (Perm (Fin 5)) := ((stab γ ⊓ stab α).subgroupOf (stab γ)).map ψ with hPb
  have hZb4 : Nat.card Zb = 4 := by rw [hZb, hZcard, hcard4]
  obtain ⟨-, hcent⟩ := card_le_four_and_cent Pb Zb hPcard hZbP hsq
  rw [Subgroup.commutator_le]
  intro n hn x hx
  obtain ⟨hnα, hnβ⟩ := hn
  have hnγ : n ∈ stab γ := Qv_le_stab_of_mem_nbrs hA hγ hnα
  have hnαs : n ∈ stab α := pCoreOf_le 2 _ hnα
  have hpn : ψ ⟨n, hnγ⟩ ∈ Pb := ⟨⟨n, hnγ⟩, ⟨hnγ, hnαs⟩, rfl⟩
  have hcn : ∀ r ∈ Zb, ψ ⟨n, hnγ⟩ * r = r * ψ ⟨n, hnγ⟩ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ Zv β := hw
    have hc : n * (w : G) = (w : G) * n :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hw').2 n hnβ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  obtain ⟨w, hw, hwn⟩ := hcent hZb4 _ hpn hcn
  have hw' : (w : G) ∈ Zv β := hw
  have hq : (w : G)⁻¹ * n ∈ Qv γ := by
    have h1 : ψ (w⁻¹ * ⟨n, hnγ⟩) = 1 := by rw [map_mul, map_inv, hwn, inv_mul_cancel]
    have := (hker _).mp h1
    simpa using this
  have hxc : ((w : G)⁻¹ * n) * x = x * ((w : G)⁻¹ * n) :=
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA γ hx).2 _ hq
  have hxw : x * (w : G)⁻¹ * x⁻¹ ∈ Zv β :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA β (hZγβ hx)) _).mp
      ((Zv β).inv_mem hw')
  rw [commutatorElement_def]
  have hn_eq : n = (w : G) * ((w : G)⁻¹ * n) := by group
  have hqx : ((w : G)⁻¹ * n) * x * ((w : G)⁻¹ * n)⁻¹ = x := by
    rw [hxc]; group
  have hcalc : n * x * n⁻¹ * x⁻¹ = (w : G) * (x * (w : G)⁻¹ * x⁻¹) :=
    calc n * x * n⁻¹ * x⁻¹
        = (w : G) * (((w : G)⁻¹ * n) * x * ((w : G)⁻¹ * n)⁻¹) * (w : G)⁻¹ * x⁻¹ := by group
      _ = (w : G) * (x * (w : G)⁻¹ * x⁻¹) := by rw [hqx]; group
  rw [hcalc]
  exact (Zv β).mul_mem hw' hxw

end F53.Stellmacher

end CFSG.Quasithin

