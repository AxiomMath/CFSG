module

public import CFSG.Quasithin.H13.A6S13828f

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem card_eq_card_map_mul {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G) :
    Nat.card K = Nat.card (K.map f) * Nat.card ↥(f.ker ⊓ K) := by
  rw [← Subgroup.relIndex_mul_card f.ker K, Subgroup.relIndex_ker]

theorem card_toSubgroup {A : Type*} [AddGroup A] (S : AddSubgroup A) :
    Nat.card ↥(AddSubgroup.toSubgroup S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_subgroupOf_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

local notation "C₂" => Subgroup.centralizer (S.V2 : Set G)

theorem bv_one : S.bv β 1 = 0 := by
  simp [bv]

theorem UH_eq_conjClosure_C2 (D : S.LineData ρ β) :
    conjClosure S.V3 S.G1 = conjClosure S.V3 C₂ := by
  refine le_antisymm (fun u hu => ?_) (conjClosure_mono le_rfl S.C2_le_G1)
  set U' := conjClosure S.V3 C₂ with hU'
  have key : ∀ x : Fin 4 → ZMod 2,
      ∃ u' : ↥(conjClosure S.V3 S.G1), (u' : G) ∈ U' ∧ S.bv β u' = x := by
    intro x
    by_cases hx : pl (S.w1 β) x = 0
    · rcases S.bv_eq_zero_or_w1 D.hβk hx with h | h
      · exact ⟨1, U'.one_mem, by rw [h, S.bv_one]⟩
      · exact ⟨⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩, le_conjClosure _ _ S.u1_mem_V3, h.symm⟩
    · obtain ⟨g', hg'1, hg'2⟩ := S.exists_GL_fix_w1 (S.pl_w1_w2_ne_zero D.hβk) hx
      obtain ⟨k, hk, hkC⟩ := S.exists_lift_C2 D.hF D.hρs D.hker D.hβk D.hβe D.hQu1 g' hg'1
      refine ⟨⟨(k : G) * S.u2 * (k : G)⁻¹, mem_conjClosure k.2 S.u2_mem_V3⟩,
        mem_conjClosure hkC S.u2_mem_V3, ?_⟩
      have := D.hβe k ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩
        ⟨_, mem_conjClosure k.2 S.u2_mem_V3⟩ rfl
      change S.bv β _ = _ at this
      rw [this, hk]
      exact hg'2
  obtain ⟨u', hu'U, hbv⟩ := key (S.bv β ⟨u, hu⟩)
  have h1 := (S.bv_eq_iff D.hβk ⟨u, hu⟩ u').1 hbv.symm
  have e : u = ((⟨u, hu⟩ * u'⁻¹ : ↥(conjClosure S.V3 S.G1)) : G) * u' := by simp
  rw [e]
  exact U'.mul_mem (le_conjClosure _ _ ((S.V1_le_V2.trans S.V2_le_V3) h1)) hu'U

variable {g : G}

theorem conj_mem_C2' (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) {k : G} (hk : k ∈ C₂) :
    g * k * g⁻¹ ∈ C₂ := by
  have := S.conj_mem_C2 (Subgroup.inv_mem _ hgN) hk
  simpa using this

theorem conjSub_UH_le_VH (D : S.LineData ρ β) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) :
    conjSub g (conjClosure S.V3 S.G1) ≤ conjClosure V S.G1 := by
  rw [S.UH_eq_conjClosure_C2 D, conjSub_le_iff]
  refine conjClosure_le fun k hk v hv => ?_
  rw [mem_conjSub, inv_inv]
  have e : g * (k * v * k⁻¹) * g⁻¹ = (g * k * g⁻¹) * (g * v * g⁻¹) * (g * k * g⁻¹)⁻¹ := by group
  rw [e]
  exact mem_conjClosure (S.C2_le_G1 (S.conj_mem_C2' hgN hk))
    ((Subgroup.mem_normalizer_iff.mp hgV v).mp (S.V3_le_V hv))

@[expose] noncomputable def U0 (g : G) : Subgroup G :=
  conjClosure S.V3 S.G1 ⊔ conjSub g (conjClosure S.V3 S.G1)

theorem V_le_U0 (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgH : g ∉ S.G1) : V ≤ S.U0 g := by
  obtain ⟨b₀, hb₀, hb₀3⟩ := S.exists_conj_V3_not_mem hgV hgH
  have hb₀V : b₀ ∈ V := by
    rw [mem_conjSub] at hb₀
    have := (Subgroup.mem_normalizer_iff.mp hgV _).mp (S.V3_le_V hb₀)
    simpa [mul_assoc] using this
  intro v hv
  by_cases hv3 : v ∈ S.V3
  · exact Subgroup.mem_sup_left (S.V3_le_UH hv3)
  · have hm := inv_mul_mem_of_relIndex_two S.relIndex_V3_V hb₀V hv hb₀3 hv3
    have e : v = b₀ * (b₀⁻¹ * v) := by group
    rw [e]
    refine (S.U0 g).mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (S.V3_le_UH hm))
    rw [mem_conjSub] at hb₀ ⊢
    exact S.V3_le_UH hb₀

theorem conj_mem_U0 (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) {k x : G} (hk : k ∈ C₂)
    (hx : x ∈ S.U0 g) : k * x * k⁻¹ ∈ S.U0 g := by
  have h1 : C₂ ≤ Subgroup.normalizer (S.U0 g : Set G) := by
    intro k hk
    have hN1 : k ∈ Subgroup.normalizer (conjClosure S.V3 S.G1 : Set G) :=
      le_normalizer_conjClosure S.V3 S.G1 (S.C2_le_G1 hk)
    have hN2 : k ∈ Subgroup.normalizer (conjSub g (conjClosure S.V3 S.G1) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact S.conj_mem_U'_of_mem hgN hk
      · intro hy
        have := S.conj_mem_U'_of_mem hgN (Subgroup.inv_mem _ hk) hy
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hN1, hN2⟩
  exact (Subgroup.mem_normalizer_iff.mp (h1 hk) x).mp hx

theorem U0_eq (D : S.LineData ρ β) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1) :
    S.U0 g = conjClosure V C₂ := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [S.UH_eq_conjClosure_C2 D]
      exact conjClosure_mono S.V3_le_V le_rfl
    · rw [S.UH_eq_conjClosure_C2 D, conjSub_le_iff]
      refine conjClosure_le fun k hk v hv => ?_
      rw [mem_conjSub, inv_inv]
      have e : g * (k * v * k⁻¹) * g⁻¹ = (g * k * g⁻¹) * (g * v * g⁻¹) * (g * k * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure (S.conj_mem_C2' hgN hk)
        ((Subgroup.mem_normalizer_iff.mp hgV v).mp (S.V3_le_V hv))
  · exact conjClosure_le fun k hk v hv => S.conj_mem_U0 hgN hk (S.V_le_U0 hgV hgH hv)

theorem conjSub_U0 (D : S.LineData ρ β) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1) :
    conjSub g (S.U0 g) = S.U0 g := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.normalizer (S.V2 : Set G) → conjSub x (conjClosure V C₂) ≤ conjClosure V C₂ := by
    intro x hxV hxN
    rw [conjSub_le_iff]
    refine conjClosure_le fun k hk v hv => ?_
    rw [mem_conjSub, inv_inv]
    have e : x * (k * v * k⁻¹) * x⁻¹ = (x * k * x⁻¹) * (x * v * x⁻¹) * (x * k * x⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure (S.conj_mem_C2' hxN hk) ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv)
  rw [S.U0_eq D hgV hgN hgH]
  refine le_antisymm (key g hgV hgN) ?_
  exact (le_conjSub_iff g).2 (key g⁻¹ (Subgroup.inv_mem _ hgV) (Subgroup.inv_mem _ hgN))

theorem conjSub_pow_UH_le_U0 (D : S.LineData ρ β) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1) (k : ℕ) :
    conjSub (g ^ k) (conjClosure S.V3 S.G1) ≤ S.U0 g := by
  induction k with
  | zero => rw [pow_zero, conjSub_one]; exact le_sup_left
  | succ k ih =>
    rw [pow_succ', conjSub_mul]
    calc conjSub g (conjSub (g ^ k) (conjClosure S.V3 S.G1)) ≤ conjSub g (S.U0 g) :=
          conjSub_mono _ ih
      _ = S.U0 g := S.conjSub_U0 D hgV hgN hgH

theorem U0_le_VH (D : S.LineData ρ β) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) : S.U0 g ≤ conjClosure V S.G1 :=
  sup_le (conjClosure_mono S.V3_le_V le_rfl) (S.conjSub_UH_le_VH D hgV hgN)

structure IsGamma (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)) : Prop where
  surj : Function.Surjective γ
  ker : ∀ v, γ v = 1 ↔ (v : G) ∈ conjClosure S.V3 S.G1
  equiv : ∀ (h : ↥S.G1) (u v : ↥(conjClosure V S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (γ v) = (wedge2 ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec (Multiplicative.toAdd (γ u))

variable {γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)}

theorem IsGamma.ker_eq (hγ : S.IsGamma ρ γ) : γ.ker = S.UHin := by
  ext v
  rw [MonoidHom.mem_ker, hγ.ker, Subgroup.mem_subgroupOf]

theorem exists_gamma_rep [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) (x : Fin 4 → ZMod 2) :
    ∃ r : ↥(conjClosure V S.G1), (r : G) ∈ conjSub g (conjClosure S.V3 S.G1) ∧
      Multiplicative.toAdd (γ r) = pl (S.w1 β) x := by
  have hline := S.line_relations D hgL hgN hgH
  by_cases hx : pl (S.w1 β) x = 0
  · exact ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one, hx]⟩
  obtain ⟨b₀, hb₀, hb₀3⟩ := S.exists_conj_V3_not_mem (S.frame.L_le hgL) hgH
  obtain ⟨r, hrU, hr⟩ := S.exists_rep D hgL hgN hb₀ hb₀3 hx
  refine ⟨r, hrU, S.Theta_injective D.hF D.hρs D.hβk D.hβe hline D.hv0 ?_⟩
  rw [hΘ, hr, S.Phi_eq_Theta D.hF D.hβk hline]

noncomputable abbrev U0in (g : G) : Subgroup ↥(conjClosure V S.G1) :=
  (S.U0 g).subgroupOf (conjClosure V S.G1)

noncomputable abbrev Rw (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)) :
    Subgroup (Multiplicative (Fin 6 → ZMod 2)) :=
  AddSubgroup.toSubgroup (plHom (S.w1 β)).range

theorem card_U0_le (D : S.LineData ρ β) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) [IsMulCommutative ↥(conjClosure V S.G1)] :
    Nat.card ↥(S.U0 g) ≤ 256 := by
  set U := conjClosure S.V3 S.G1 with hU
  set U' := conjSub g U with hU'
  have hU'VH := S.conjSub_UH_le_VH D hgV hgN
  have hUVH : U ≤ conjClosure V S.G1 := conjClosure_mono S.V3_le_V le_rfl
  have hcomm : ∀ a ∈ conjClosure V S.G1, ∀ b ∈ conjClosure V S.G1, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(conjClosure V S.G1))).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hN : U' ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e : ∀ y ∈ U, x * y * x⁻¹ = y := fun y hy => by
      rw [hcomm x (hU'VH hx) y (hUVH hy), mul_inv_cancel_right]
    constructor
    · intro hy
      rw [e y hy]
      exact hy
    · intro hy
      have hy' : y ∈ conjClosure V S.G1 := by
        have h1 := hcomm x (hU'VH hx)
        by_contra hcon
        exact hcon (by
          have : x⁻¹ * (x * y * x⁻¹) * x = y := by group
          rw [← this]
          have h2 := hUVH hy
          exact (conjClosure V S.G1).mul_mem ((conjClosure V S.G1).mul_mem
            ((conjClosure V S.G1).inv_mem (hU'VH hx)) h2) (hU'VH hx))
      have e2 : x * y * x⁻¹ = y := by rw [hcomm x (hU'VH hx) y hy', mul_inv_cancel_right]
      rw [← e2]
      exact hy
  have h1 := card_sup_mul_card_inf' hN
  have hcard : Nat.card ↥U = 32 := D.hcard
  have hcard' : Nat.card ↥U' = 32 := by rw [hU', CosetGeom.card_conjSub, hcard]
  have h2 := S.relIndex_U'_le hgN hcard
  have h3 := Subgroup.relIndex_mul_card (U' ⊓ U) U'
  rw [inf_eq_left.2 inf_le_left, hcard'] at h3
  have hsup : S.U0 g = U' ⊔ U := sup_comm _ _
  rw [hsup]
  have h4 : 4 ≤ Nat.card ↥(U' ⊓ U) := by nlinarith
  rw [hcard', hcard] at h1
  nlinarith

theorem map_gamma_U0 [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    (S.U0in g).map γ = S.Rw β := by
  have hgV := S.frame.L_le hgL
  have hle : S.Rw β ≤ (S.U0in g).map γ := by
    rintro y ⟨x, rfl⟩
    obtain ⟨r, hrU, hr⟩ := S.exists_gamma_rep D hgL hgN hgH hΘ x
    exact ⟨r, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hrU),
      Multiplicative.toAdd.injective (by rw [hr]; rfl)⟩
  have hw1 : S.w1 β ≠ 0 := ((pl_ne_zero_iff _ _).1 (S.pl_w1_w2_ne_zero D.hβk)).1
  have hR : Nat.card ↥(S.Rw β) = 8 := by rw [card_toSubgroup, card_plHom_range hw1]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 := card_eq_card_map_mul γ (S.U0in g)
  rw [hγ.ker_eq] at h1
  have hUin : S.UHin ⊓ S.U0in g = S.UHin := by
    refine inf_eq_left.2 fun x hx => Subgroup.mem_subgroupOf.2 ?_
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx)
  rw [hUin] at h1
  have h2 : Nat.card ↥(S.U0in g) = Nat.card ↥(S.U0 g) :=
    card_subgroupOf_of_le (S.U0_le_VH D hgV hgN)
  have h3 : Nat.card ↥S.UHin = 32 := by
    rw [card_subgroupOf_of_le (conjClosure_mono S.V3_le_V le_rfl)]
    exact D.hcard
  have h4 := S.card_U0_le D hgN hgV
  rw [hR]
  nlinarith

theorem card_U0 [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    Nat.card ↥(S.U0 g) = 256 := by
  have hgV := S.frame.L_le hgL
  have h1 := card_eq_card_map_mul γ (S.U0in g)
  rw [hγ.ker_eq, S.map_gamma_U0 D hgL hgN hgH hγ hΘ] at h1
  have hUin : S.UHin ⊓ S.U0in g = S.UHin := by
    refine inf_eq_left.2 fun x hx => Subgroup.mem_subgroupOf.2 ?_
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hx)
  rw [hUin] at h1
  have hw1 : S.w1 β ≠ 0 := ((pl_ne_zero_iff _ _).1 (S.pl_w1_w2_ne_zero D.hβk)).1
  rw [← card_subgroupOf_of_le (S.U0_le_VH D hgV hgN), h1, card_toSubgroup,
    card_plHom_range hw1, card_subgroupOf_of_le (conjClosure_mono S.V3_le_V le_rfl),
    D.hcard]

@[expose] noncomputable def Xs (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2))
    (γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2)) : Subgroup G :=
  ((AddSubgroup.toSubgroup (plS (S.w1 β) (S.w2 β))).comap γ).map (conjClosure V S.G1).subtype

theorem mem_Xs {x : G} : x ∈ S.Xs β γ ↔
    ∃ hx : x ∈ conjClosure V S.G1, Multiplicative.toAdd (γ ⟨x, hx⟩) ∈ plS (S.w1 β) (S.w2 β) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Xs_le_VH : S.Xs β γ ≤ conjClosure V S.G1 := fun _ hx => (S.mem_Xs.1 hx).1

theorem card_Xs (D : S.LineData ρ β) (hγ : S.IsGamma ρ γ) : Nat.card ↥(S.Xs β γ) = 1024 := by
  rw [Xs, Subgroup.card_map_of_injective (conjClosure V S.G1).subtype_injective]
  have h1 := card_eq_card_map_mul γ
    ((AddSubgroup.toSubgroup (plS (S.w1 β) (S.w2 β))).comap γ)
  rw [Subgroup.map_comap_eq_self_of_surjective hγ.surj,
    inf_eq_left.2 (MonoidHom.ker_le_comap γ _), hγ.ker_eq, card_toSubgroup,
    card_plS (S.pl_w1_w2_ne_zero D.hβk),
    card_subgroupOf_of_le (conjClosure_mono S.V3_le_V le_rfl), D.hcard] at h1
  exact h1

theorem U0_le_Xs [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v) :
    S.U0 g ≤ S.Xs β γ := by
  intro x hx
  have hxV := S.U0_le_VH D (S.frame.L_le hgL) hgN hx
  have h1 : γ ⟨x, hxV⟩ ∈ S.Rw β := by
    rw [← S.map_gamma_U0 D hgL hgN hgH hγ hΘ]
    exact ⟨⟨x, hxV⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  obtain ⟨y, hy⟩ := h1
  refine S.mem_Xs.2 ⟨hxV, ?_⟩
  rw [← hy]
  exact pl_mem_plS_left _ _ y

variable {c : ↥S.G1}

theorem rv_w1_of_conj (D : S.LineData ρ β) (hcu : (c : G) * S.u1 * (c : G)⁻¹ = S.u1 * S.u2) :
    S.rv ρ c (S.w1 β) = S.w1 β + S.w2 β := by
  have hu1 := S.V3_le_UH S.u1_mem_V3
  have hu2 := S.V3_le_UH S.u2_mem_V3
  have h1 := D.hβe c ⟨S.u1, hu1⟩ ⟨S.u1 * S.u2, (conjClosure S.V3 S.G1).mul_mem hu1 hu2⟩ hcu.symm
  change S.bv β ((⟨S.u1, hu1⟩ : ↥(conjClosure S.V3 S.G1)) * ⟨S.u2, hu2⟩) =
    S.rv ρ c (S.w1 β) at h1
  rw [bv_mul] at h1
  exact h1.symm

theorem rv_w1_mem_span (D : S.LineData ρ β) (hc3 : (c : G) * S.u1 * (c : G)⁻¹ ∈ S.V3) :
    S.rv ρ c (S.w1 β) = 0 ∨ S.rv ρ c (S.w1 β) = S.w1 β ∨ S.rv ρ c (S.w1 β) = S.w2 β ∨
      S.rv ρ c (S.w1 β) = S.w1 β + S.w2 β := by
  have hu1 := S.V3_le_UH S.u1_mem_V3
  have hcu : (c : G) * S.u1 * (c : G)⁻¹ ∈ conjClosure S.V3 S.G1 := S.V3_le_UH hc3
  have h1 := D.hβe c ⟨S.u1, hu1⟩ ⟨_, hcu⟩ rfl
  change S.bv β ⟨_, hcu⟩ = S.rv ρ c (S.w1 β) at h1
  obtain ⟨s₁, s₂, hs⟩ := S.bv_V3 D.hβk ⟨_, hcu⟩ hc3
  rw [← h1, hs]
  rcases zmodTwo_cases s₁ with h | h <;> rcases zmodTwo_cases s₂ with h' | h' <;> simp [h, h']

theorem conjSub_U0_le_Xs [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    (hc3 : (c : G) * S.u1 * (c : G)⁻¹ ∈ S.V3) :
    conjSub (c : G) (S.U0 g) ≤ S.Xs β γ := by
  intro y hy
  rw [mem_conjSub] at hy
  set u := (c : G)⁻¹ * y * c with hu
  have huX := S.U0_le_Xs D hgL hgN hgH hγ hΘ hy
  obtain ⟨huV, hu'⟩ := S.mem_Xs.1 huX
  have hyV : y ∈ conjClosure V S.G1 := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1 c.2) u).mp huV
    rwa [hu, show (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ = y by group] at this
  have hγy := hγ.equiv c ⟨u, huV⟩ ⟨y, hyV⟩ (by
    show y = (c : G) * u * (c : G)⁻¹
    simp only [hu]
    group)
  have h1 : γ ⟨u, huV⟩ ∈ S.Rw β := by
    rw [← S.map_gamma_U0 D hgL hgN hgH hγ hΘ]
    exact ⟨⟨u, huV⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  obtain ⟨x, hx⟩ := h1
  refine S.mem_Xs.2 ⟨hyV, ?_⟩
  rw [hγy, show Multiplicative.toAdd (γ ⟨u, huV⟩) = pl (S.w1 β) x from hx.symm,
    wedge2_mulVec_pl]
  change pl (S.rv ρ c (S.w1 β)) (S.rv ρ c x) ∈ _
  exact pl_mem_plS_of_span (S.rv_w1_mem_span D hc3) _

theorem Xs_le_sup [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β)
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    (hγ : S.IsGamma ρ γ)
    (hΘ : ∀ v, S.Theta ρ β D.hF (Multiplicative.toAdd (γ v)) = S.cls v)
    (hcu : (c : G) * S.u1 * (c : G)⁻¹ = S.u1 * S.u2) :
    S.Xs β γ ≤ S.U0 g ⊔ conjSub (c : G) (S.U0 g) := by
  have hgV := S.frame.L_le hgL
  have hmap := S.map_gamma_U0 D hgL hgN hgH hγ hΘ
  have hpre : ∀ a, ∃ u : ↥(conjClosure V S.G1), (u : G) ∈ S.U0 g ∧
      Multiplicative.toAdd (γ u) = pl (S.w1 β) a := by
    intro a
    have : Multiplicative.ofAdd (pl (S.w1 β) a) ∈ (S.U0in g).map γ := by
      rw [hmap]
      exact ⟨a, rfl⟩
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, by rw [hu']; rfl⟩
  intro x hx
  obtain ⟨hxV, hxS⟩ := S.mem_Xs.1 hx
  rw [← plS_add_right] at hxS
  obtain ⟨a, b, hab⟩ := mem_plS.1 hxS
  obtain ⟨u, huU, hu⟩ := hpre a
  obtain ⟨u', hu'U, hu'⟩ := hpre (S.rv ρ c⁻¹ b)
  set v : ↥(conjClosure V S.G1) :=
    ⟨(c : G) * u' * (c : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure V S.G1 c.2) u').mp u'.2⟩ with hv
  have hγv := hγ.equiv c u' v rfl
  have hvc : (v : G) ∈ conjSub (c : G) (S.U0 g) := by
    rw [mem_conjSub, hv]
    simpa [mul_assoc] using hu'U
  have hγv' : Multiplicative.toAdd (γ v) = pl (S.w1 β + S.w2 β) b := by
    rw [hγv, hu', wedge2_mulVec_pl]
    change pl (S.rv ρ c (S.w1 β)) (S.rv ρ c (S.rv ρ c⁻¹ b)) = _
    rw [S.rv_w1_of_conj D hcu]
    congr 1
    have := S.rv_inv_rv (ρ := ρ) c⁻¹ b
    rwa [inv_inv] at this
  set q : ↥(conjClosure V S.G1) := ⟨x, hxV⟩ * (u * v)⁻¹ with hq
  have hq1 : γ q = 1 := by
    rw [hq, map_mul, map_inv, map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_mul, hu, hγv', ← hab, toAdd_one]
    exact add_neg_cancel _
  have hqU : (q : G) ∈ S.U0 g := Subgroup.mem_sup_left ((hγ.ker q).1 hq1)
  have e : x = (q : G) * u * v := by
    rw [hq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hqU)
    (Subgroup.mem_sup_left huU)) (Subgroup.mem_sup_right hvc)

end Setting4

end CFSG.Quasithin.H13.A6

