module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom Equiv Mod6

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_two {N K : Subgroup G} (h : N.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (hna : a ∉ N) (hnb : b ∉ N) : a⁻¹ * b ∈ N := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h
  have key : ∀ z : G, (hz : z ∈ K) → z ∉ N → (⟨z⁻¹, K.inv_mem hz⟩ : ↥K) * c ∈ N.subgroupOf K := by
    intro z hz hzN
    have hx : (⟨z⁻¹, K.inv_mem hz⟩ : ↥K) ∉ N.subgroupOf K := fun h' =>
      hzN (by simpa using N.inv_mem (Subgroup.mem_subgroupOf.mp h'))
    rcases hc ⟨z⁻¹, K.inv_mem hz⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hx
  have h1 := key a ha hna
  have h2 := key b hb hnb
  have h3 := (N.subgroupOf K).mul_mem h1 ((N.subgroupOf K).inv_mem h2)
  have h4 : (⟨a⁻¹, K.inv_mem ha⟩ : ↥K) * c * ((⟨b⁻¹, K.inv_mem hb⟩ : ↥K) * c)⁻¹ =
      ⟨a⁻¹, K.inv_mem ha⟩ * ⟨b⁻¹, K.inv_mem hb⟩⁻¹ := by group
  rw [h4] at h3
  simpa using Subgroup.mem_subgroupOf.mp h3

omit [Finite G] in
theorem sq_mem_of_relIndex_two {N K : Subgroup G} (h : N.relIndex K = 2) {x : G}
    (hx : x ∈ K) : x * x ∈ N := by
  by_cases hN : x ∈ N
  · exact N.mul_mem hN hN
  · have hN' : x⁻¹ ∉ N := fun h' => hN (by simpa using N.inv_mem h')
    have := inv_mul_mem_of_relIndex_two h (K.inv_mem hx) hx hN' hN
    simpa using this

theorem smul_mem_nbrs_of_mem_stab (g : ↥(H ⊔ M)) {δ w : Geo H M} (hg : (g : G) ∈ stab δ)
    (hw : w ∈ nbrs δ) : g • w ∈ nbrs δ := by
  have := (smul_mem_nbrs_iff g (l := δ) (δ := w)).mpr hw
  rwa [smul_eq_of_mem_stab hg] at this

open Classical in
noncomputable def chi (δ : Geo H M) (x : G) : Bool :=
  decide (x ∉ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G))

omit [Finite G] in
theorem chi_eq_false {δ : Geo H M} {x : G} (h : x ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)) :
    chi δ x = false := by
  simp [chi, h]

omit [Finite G] in
theorem chi_eq_true {δ : Geo H M} {x : G}
    (h : x ∉ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)) : chi δ x = true := by
  simp [chi, h]

structure Frame (δ l : Geo H M) where
  D : Dict6 (stab δ) (Vn δ) (Yv δ)
  lv : Fin 3 → Geo H M
  lv0 : lv 0 = l
  lv_mem : ∀ i, lv i ∈ nbrs δ
  lv_inj : Function.Injective lv
  lv_surj : ∀ w ∈ nbrs δ, ∃ i, lv i = w
  hZ : ∀ i, Zv (lv i) = D.Ψ (usub i)
  n : Fin 3
  hn : D.HasK n
  perm_exists : ∀ g : ↥(H ⊔ M), (g : G) ∈ stab δ → ∃ σ : Perm (Fin 3), ∀ i, g • lv i = lv (σ i)
  acts : ∀ (g : ↥(H ⊔ M)) (σ : Perm (Fin 3)), (g : G) ∈ stab δ → (∀ i, g • lv i = lv (σ i)) →
    D.Acts (g : G) σ (chi δ (g : G))

omit [Finite G] in
theorem Frame.Zv_eq {δ l : Geo H M} (F : Frame δ l) : Zv l = F.D.Ψ (usub 0) :=
  (congrArg Zv F.lv0).symm.trans (F.hZ 0)

omit [Finite G] in
theorem card_Vn_eq {δ δ' : Geo H M} (hδ : vtype δ = true) (hδ' : vtype δ' = true) :
    Nat.card (Vn δ) = Nat.card (Vn δ') := by
  obtain ⟨g, hg⟩ := exists_smul_of_vtype_eq (hδ.trans hδ'.symm)
  rw [hg, Vn_smul]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom)
    (MulAut.conj (g : G)).injective).symm

namespace Sit43

variable {α : Geo H M} {δ l : Geo H M}

theorem exists_d (hA : F53Amalgam H M S) (hδ : vtype δ = true) :
    ∃ d : G, d ∈ stab δ ∧ d ^ 3 = 1 ∧ d ≠ 1 := by
  obtain ⟨ψ, hψs, -⟩ := exists_quotHom_true hA hδ
  have h3 : 3 ∣ Nat.card ↥(stab δ) := by
    have h := Subgroup.card_dvd_of_surjective hψs
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact (by decide : 3 ∣ Nat.factorial 3).trans h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stab δ)) 3 h3
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem smul_ne_self (hA : F53Amalgam H M S) (hl : l ∈ nbrs δ) {d : G} (hd : d ∈ stab δ)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : (⟨d, stab_le δ hd⟩ : ↥(H ⊔ M)) • l ≠ l := by
  intro h
  have hdl : d ∈ stab l := mem_stab_of_smul_eq h
  have hE : d ∈ stab l ⊓ stab δ := ⟨hdl, hd⟩
  have hP : IsPGroup 2 (stab l ⊓ stab δ : Subgroup G) :=
    (sylow_stab_inf_left hA (nbrs_symm hl)).2.1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨d, hE⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  rw [Subgroup.orderOf_mk, h3] at hk
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have : (4 : ℕ) ∣ 3 := by
      rw [hk]
      exact ⟨2 ^ k, by ring⟩
    omega

theorem exists_rot (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ∃ g₀ : ↥(H ⊔ M), (g₀ : G) ∈ stab δ ∧ g₀ ^ 3 = 1 ∧ g₀ • l ≠ l ∧
      S29.Sit29 H M S l (g₀ • l) (g₀ ^ 2 • l) δ := by
  obtain ⟨d, hd, hd3, hd1⟩ := exists_d hA hδ
  set g₀ : ↥(H ⊔ M) := ⟨d, stab_le δ hd⟩ with hg₀
  have hg0δ : (g₀ : G) ∈ stab δ := hd
  have hg3 : g₀ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hne1 : g₀ • l ≠ l := smul_ne_self hA hl hd hd3 hd1
  have hne2 : g₀ ^ 2 • l ≠ l := by
    intro h
    apply hne1
    have : g₀ ^ 3 • l = g₀ • l := by
      rw [pow_succ', mul_smul, h]
    rw [hg3, one_smul] at this
    exact this.symm
  have hne3 : g₀ • l ≠ g₀ ^ 2 • l := by
    intro h
    apply hne1
    have : g₀ • l = g₀ • (g₀ • l) := by
      calc g₀ • l = g₀ ^ 2 • l := h
        _ = g₀ • (g₀ • l) := by rw [pow_two, mul_smul]
    exact (smul_left_cancel g₀ this).symm
  have hg2δ : ((g₀ ^ 2 : ↥(H ⊔ M)) : G) ∈ stab δ := by
    simpa using Subgroup.pow_mem _ hg0δ 2
  obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl
  exact ⟨g₀, hg0δ, hg3, hne1, ⟨h29.amalg, h29.h28, h29.h26, h29.b1, h29.adj, h29.vα, h29.bα,
    h29.hz, h29.hmod, smul_mem_nbrs_of_mem_stab g₀ hg0δ hl, smul_mem_nbrs_of_mem_stab _ hg2δ hl,
    hne1.symm, hne2.symm, hne3⟩⟩

theorem Yv_le_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : Yv δ ≤ ⁅Zv l, Qv δ⁆ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h1 := hs.Yv_eq_comm_comm hA h26 hδ hl
  rw [hs.comm_Qv_eq hA h26 hδ hl, h1]
  exact comm_comm_le_comm (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth

theorem comm_le_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : ⁅Zv l, Qv δ⁆ ≤ Zv l := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  rw [hs.comm_Qv_eq hA h26 hδ hl]
  exact comm_le (quot_stab_five hA hlv) (sylow_stab_inf_left hA (nbrs_symm hl))
    (hs.of_vtype_false hlv).orth

theorem relIndex_Yv_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : (Yv δ).relIndex ⁅Zv l, Qv δ⁆ = 2 := by
  have h1 := Subgroup.relIndex_mul_card (Yv δ) ⁅Zv l, Qv δ⁆
  rw [inf_eq_left.mpr (hs.Yv_le_comm hA h26 hδ hl), hs.card_Yv hA h26 hδ,
    hs.card_comm_Qv hA h26 hδ hl] at h1
  omega

theorem relIndex_comm_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : (⁅Zv l, Qv δ⁆).relIndex (Zv l) = 2 := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have h1 := Subgroup.relIndex_mul_card ⁅Zv l, Qv δ⁆ (Zv l)
  rw [inf_eq_left.mpr (hs.comm_le_Zv hA h26 hδ hl), hs.card_comm_Qv hA h26 hδ hl,
    hs.card_Zv_false hlv] at h1
  omega

theorem exists_basis (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ∃ u₀ u₁ : G, u₀ ∈ ⁅Zv l, Qv δ⁆ ∧ u₀ ∉ Yv δ ∧ u₁ ∈ Zv l ∧ u₁ ∉ ⁅Zv l, Qv δ⁆ := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  have hu0 : ∃ u₀ ∈ ⁅Zv l, Qv δ⁆, u₀ ∉ Yv δ := by
    by_contra h
    push Not at h
    have hle : ⁅Zv l, Qv δ⁆ ≤ Yv δ := h
    have := Subgroup.card_le_of_le hle
    rw [hs.card_comm_Qv hA h26 hδ hl, hs.card_Yv hA h26 hδ] at this
    omega
  have hu1 : ∃ u₁ ∈ Zv l, u₁ ∉ ⁅Zv l, Qv δ⁆ := by
    by_contra h
    push Not at h
    have hle : Zv l ≤ ⁅Zv l, Qv δ⁆ := h
    have := Subgroup.card_le_of_le hle
    rw [hs.card_comm_Qv hA h26 hδ hl, hs.card_Zv_false hlv] at this
    omega
  obtain ⟨u₀, h0, h0'⟩ := hu0
  obtain ⟨u₁, h1, h1'⟩ := hu1
  exact ⟨u₀, u₁, h0, h0', h1, h1'⟩

theorem comm_Zv_inf_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ⁅Zv l, (stab l ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G)⁆ = Yv δ := by
  have hQδl : Qv δ ≤ stab l := Qv_le_stab_of_mem_nbrs hA hl
  have hQstl : Qst δ ≤ stab l := (inf_le_left : Qst δ ≤ Qv δ).trans hQδl
  have h1 := commutator_sup_eq_of_centralizes (Z := Zv l) (C := Qv l) (T := Qst δ)
    (fun c hc z hz => ((Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA l hc) z hz)).symm)
    (hQstl.trans (le_normalizer_pCoreOf 2 (stab l))) (hQstl.trans (stab_le_normalizer_Zv hA l))
  rw [← hs.Qv_sup_Qst hA h26 hδ hl, h1]
  exact hs.comm_Zv_Qst hA h26 hδ hl

omit [Finite G] in
theorem Zv_le_Vn_nbrs (hl : l ∈ nbrs δ) : Zv l ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) l hl le_rfl

theorem Zv_decomp (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {u₀ u₁ : G} (h0 : u₀ ∈ ⁅Zv l, Qv δ⁆)
    (h0' : u₀ ∉ Yv δ) (h1 : u₁ ∈ Zv l) (h1' : u₁ ∉ ⁅Zv l, Qv δ⁆) (hcomm : u₀ * u₁ = u₁ * u₀) :
    ∀ z ∈ Zv l, ∃ a b : Multiplicative (ZMod 2), ∃ y ∈ Yv δ,
      z = (if a = 1 then 1 else u₀) * (if b = 1 then 1 else u₁) * y := by
  intro z hz
  have hne : (g1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  by_cases hzC : z ∈ ⁅Zv l, Qv δ⁆
  · by_cases hzY : z ∈ Yv δ
    · exact ⟨1, 1, z, hzY, by simp⟩
    · have := inv_mul_mem_of_relIndex_two (hs.relIndex_Yv_comm hA h26 hδ hl) h0 hzC h0' hzY
      refine ⟨g1, 1, _, this, ?_⟩
      simp [hne]
  · have hc := inv_mul_mem_of_relIndex_two (hs.relIndex_comm_Zv hA h26 hδ hl) h1 hz h1' hzC
    by_cases hcY : u₁⁻¹ * z ∈ Yv δ
    · refine ⟨1, g1, _, hcY, ?_⟩
      simp [hne]
    · have := inv_mul_mem_of_relIndex_two (hs.relIndex_Yv_comm hA h26 hδ hl) h0 hc h0' hcY
      refine ⟨g1, g1, _, this, ?_⟩
      simp only [hne, ↓reduceIte]
      calc z = u₁ * u₀ * (u₀⁻¹ * (u₁⁻¹ * z)) := by group
        _ = u₀ * u₁ * (u₀⁻¹ * (u₁⁻¹ * z)) := by rw [hcomm]

theorem edge_u0 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {u₀ : G} (h0 : u₀ ∈ ⁅Zv l, Qv δ⁆) {h : G}
    (hh : h ∈ stab l ⊓ stab δ) : h * u₀ * h⁻¹ * u₀⁻¹ ∈ Yv δ := by
  have h1 : ⁅h, u₀⁆ ∈ ⁅stab l ⊓ stab δ, ⁅Zv l, Qv δ⁆⁆ := Subgroup.commutator_mem_commutator hh h0
  rw [Subgroup.commutator_comm, hs.comm_Qv_eq hA h26 hδ hl,
    ← hs.Yv_eq_comm_comm hA h26 hδ hl] at h1
  exact h1

theorem edge_C (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {z : G} (hz : z ∈ Zv l) {h : G}
    (hh : h ∈ stab l ⊓ stab δ) : h * z * h⁻¹ * z⁻¹ ∈ ⁅Zv l, Qv δ⁆ := by
  have h1 : ⁅h, z⁆ ∈ ⁅stab l ⊓ stab δ, Zv l⁆ := Subgroup.commutator_mem_commutator hh hz
  rw [Subgroup.commutator_comm, ← hs.comm_Qv_eq hA h26 hδ hl] at h1
  exact h1

theorem edge_Cy (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {z : G} (hz : z ∈ Zv l) {h : G}
    (hh : h ∈ stab l ⊓ stab δ) (hhC : h ∈ Subgroup.centralizer (Yv δ : Set G)) :
    h * z * h⁻¹ * z⁻¹ ∈ Yv δ := by
  have h1 : ⁅h, z⁆ ∈ ⁅(stab l ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G), Zv l⁆ :=
    Subgroup.commutator_mem_commutator ⟨hh, hhC⟩ hz
  rw [Subgroup.commutator_comm, hs.comm_Zv_inf_centralizer hA h26 hδ hl] at h1
  exact h1

theorem mem_centralizer_of_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {u₀ u₁ : G}
    (h0 : u₀ ∈ ⁅Zv l, Qv δ⁆) (h0' : u₀ ∉ Yv δ) (h1 : u₁ ∈ Zv l) (h1' : u₁ ∉ ⁅Zv l, Qv δ⁆)
    {h : G} (hh : h ∈ stab l ⊓ stab δ) (hY1 : h * u₁ * h⁻¹ * u₁⁻¹ ∈ Yv δ) :
    h ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := by
  by_contra hhC
  have hV := isElemAbelian_Vn hA hb δ
  have hVc : ∀ a ∈ Vn δ, ∀ b ∈ Vn δ, a * b = b * a := fun a ha b hb' =>
    isElemAbelian_comm hV ha hb'
  have hYV : Yv δ ≤ Vn δ := (Yv_le_Zv hl).trans (Zv_le_Vn_nbrs hl)
  have hCV : ⁅Zv l, Qv δ⁆ ≤ Vn δ := (hs.comm_le_Zv hA h26 hδ hl).trans (Zv_le_Vn_nbrs hl)
  have hnY := hs.stab_le_normalizer_Yv hA h26 hδ
  have hhδ : h ∈ stab δ := hh.2
  have hY' : ∀ y ∈ Yv δ, h * y * h⁻¹ ∈ Yv δ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hnY hhδ) y).mp hy
  have hmul : ∀ a b : G, a ∈ Vn δ → h * a * h⁻¹ * a⁻¹ ∈ Yv δ → h * b * h⁻¹ * b⁻¹ ∈ Yv δ →
      h * (a * b) * h⁻¹ * (a * b)⁻¹ ∈ Yv δ := by
    intro a b ha hab hbb
    have e : h * (a * b) * h⁻¹ * (a * b)⁻¹ =
        (h * a * h⁻¹ * a⁻¹) * (a * (h * b * h⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    refine (Yv δ).mul_mem hab ?_
    have := hVc a ha _ (hYV hbb)
    rw [this]
    simpa using hbb
  have hcomm : u₀ * u₁ = u₁ * u₀ := hVc _ (hCV h0) _ (Zv_le_Vn_nbrs hl h1)
  have hzall : ∀ z ∈ Zv l, h * z * h⁻¹ * z⁻¹ ∈ Yv δ := by
    intro z hz
    obtain ⟨a, b, y, hy, rfl⟩ := hs.Zv_decomp hA h26 hδ hl h0 h0' h1 h1' hcomm z hz
    have p0 : h * (if a = 1 then 1 else u₀) * h⁻¹ * (if a = 1 then 1 else u₀)⁻¹ ∈ Yv δ := by
      split_ifs
      · simp
      · exact hs.edge_u0 hA h26 hδ hl h0 hh
    have p1 : h * (if b = 1 then 1 else u₁) * h⁻¹ * (if b = 1 then 1 else u₁)⁻¹ ∈ Yv δ := by
      split_ifs
      · simp
      · exact hY1
    have q0 : (if a = 1 then 1 else u₀) ∈ Vn δ := by
      split_ifs
      · exact (Vn δ).one_mem
      · exact hCV h0
    have q1 : (if b = 1 then 1 else u₁) ∈ Vn δ := by
      split_ifs
      · exact (Vn δ).one_mem
      · exact Zv_le_Vn_nbrs hl h1
    have p2 : h * y * h⁻¹ * y⁻¹ ∈ Yv δ := (Yv δ).mul_mem (hY' y hy) ((Yv δ).inv_mem hy)
    exact hmul _ _ ((Vn δ).mul_mem q0 q1) (hmul _ _ q0 p0 p1) p2
  have hle : ⁅Zv l, Qv δ⁆ ≤ Yv δ := by
    rw [hs.comm_Qv_eq hA h26 hδ hl, Subgroup.commutator_le]
    intro z hz e he
    have key : e * z * e⁻¹ * z⁻¹ ∈ Yv δ := by
      by_cases heC : e ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)
      · exact hs.edge_Cy hA h26 hδ hl hz he heC.2
      · have h2 := (hs.relIndex_centralizer_Yv hA h26 hδ hl).1
        have hk := inv_mul_mem_of_relIndex_two h2 hhδ he.2 hhC heC
        have hkE : h⁻¹ * e ∈ stab l ⊓ stab δ := (stab l ⊓ stab δ).mul_mem
          ((stab l ⊓ stab δ).inv_mem hh) he
        have e1 : e * z * e⁻¹ * z⁻¹ =
            (h * ((h⁻¹ * e) * z * (h⁻¹ * e)⁻¹ * z⁻¹) * h⁻¹) * (h * z * h⁻¹ * z⁻¹) := by group
        rw [e1]
        exact (Yv δ).mul_mem (hY' _ (hs.edge_Cy hA h26 hδ hl hz hkE hk.2)) (hzall z hz)
    have : ⁅z, e⁆ = (e * z * e⁻¹ * z⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this]
    exact (Yv δ).inv_mem key
  have := Subgroup.card_le_of_le hle
  rw [hs.card_comm_Qv hA h26 hδ hl, hs.card_Yv hA h26 hδ] at this
  omega

open Classical in
theorem edge_action (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {u₀ u₁ : G}
    (h0 : u₀ ∈ ⁅Zv l, Qv δ⁆) (h0' : u₀ ∉ Yv δ) (h1 : u₁ ∈ Zv l) (h1' : u₁ ∉ ⁅Zv l, Qv δ⁆)
    {h : G} (hh : h ∈ stab l ⊓ stab δ) :
    h * u₀ * h⁻¹ * u₀⁻¹ ∈ Yv δ ∧
      h * u₁ * h⁻¹ * (u₁ * (if h ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) then 1 else u₀))⁻¹
        ∈ Yv δ := by
  refine ⟨hs.edge_u0 hA h26 hδ hl h0 hh, ?_⟩
  by_cases hC : h ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)
  · simp only [hC, ↓reduceIte, mul_one]
    exact hs.edge_Cy hA h26 hδ hl h1 hh hC.2
  · simp only [hC, ↓reduceIte]
    have hV := isElemAbelian_Vn hA hb δ
    have hVc : ∀ a ∈ Vn δ, ∀ b ∈ Vn δ, a * b = b * a := fun a ha b hb' =>
      isElemAbelian_comm hV ha hb'
    have hCV : ⁅Zv l, Qv δ⁆ ≤ Vn δ := (hs.comm_le_Zv hA h26 hδ hl).trans (Zv_le_Vn_nbrs hl)
    have hcomm : Commute u₀ u₁ := hVc _ (hCV h0) _ (Zv_le_Vn_nbrs hl h1)
    have hc : h * u₁ * h⁻¹ * u₁⁻¹ ∈ ⁅Zv l, Qv δ⁆ := hs.edge_C hA h26 hδ hl h1 hh
    have hcY : h * u₁ * h⁻¹ * u₁⁻¹ ∉ Yv δ := fun hY =>
      hC (hs.mem_centralizer_of_comm hA h26 hb hδ hl h0 h0' h1 h1' hh hY)
    have hmem := inv_mul_mem_of_relIndex_two (hs.relIndex_Yv_comm hA h26 hδ hl) h0 hc h0' hcY
    have hcc : (h * u₁ * h⁻¹ * u₁⁻¹) * u₀⁻¹ = u₀⁻¹ * (h * u₁ * h⁻¹ * u₁⁻¹) :=
      hVc _ (hCV hc) _ ((Vn δ).inv_mem (hCV h0))
    have e : h * u₁ * h⁻¹ * (u₁ * u₀)⁻¹ = u₀⁻¹ * (h * u₁ * h⁻¹ * u₁⁻¹) := by
      rw [← hcc]
      have h3 : u₁ * u₀⁻¹ * u₁⁻¹ = u₀⁻¹ := by
        rw [← hcomm.inv_left.eq]; group
      calc h * u₁ * h⁻¹ * (u₁ * u₀)⁻¹
          = (h * u₁ * h⁻¹ * u₁⁻¹) * (u₁ * u₀⁻¹ * u₁⁻¹) := by group
        _ = (h * u₁ * h⁻¹ * u₁⁻¹) * u₀⁻¹ := by rw [h3]
    rw [e]
    exact hmem

omit [Finite G] in
theorem conj_ite (g x : G) (c : Prop) [Decidable c] :
    g * (if c then 1 else x) * g⁻¹ = if c then 1 else g * x * g⁻¹ := by
  split_ifs <;> group

theorem exists_frame (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) : Nonempty (Frame δ l) := by
  have hlv : vtype l = false := vtype_false_of_adj hδ hl
  obtain ⟨g₀, hg0, hg3, hne, hs29⟩ := hs.exists_rot hA h26 hδ hl
  obtain ⟨u₀, u₁, h0, h0', h1, h1'⟩ := hs.exists_basis hA h26 hδ hl
  set d : G := (g₀ : G) with hd
  have hdδ : ∀ k : ℕ, d ^ k ∈ stab δ := fun k => Subgroup.pow_mem _ hg0 k
  have hd3 : d ^ 3 = 1 := by simpa [hd] using congrArg Subtype.val hg3
  let lv : Fin 3 → Geo H M := fun i => g₀ ^ (i : ℕ) • l
  have hcoe : ∀ k : ℕ, (((g₀ ^ k : ↥(H ⊔ M)) : G)) = d ^ k := fun k => by simp [hd]
  have lv_mem : ∀ i, lv i ∈ nbrs δ := fun i =>
    smul_mem_nbrs_of_mem_stab _ (by rw [hcoe]; exact hdδ _) hl
  have lv0 : lv 0 = l := by simp [lv]
  have lv1 : lv 1 = g₀ • l := by simp [lv]
  have lv2 : lv 2 = g₀ ^ 2 • l := by simp [lv]
  have lv_inj : Function.Injective lv := by
    have n01 : lv 0 ≠ lv 1 := by rw [lv0, lv1]; exact hs29.ne₁₂
    have n02 : lv 0 ≠ lv 2 := by rw [lv0, lv2]; exact hs29.ne₁₃
    have n12 : lv 1 ≠ lv 2 := by rw [lv1, lv2]; exact hs29.ne₂₃
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hij n01 | exact absurd hij.symm n01
      | exact absurd hij n02 | exact absurd hij.symm n02
      | exact absurd hij n12 | exact absurd hij.symm n12
  have lv_surj : ∀ w ∈ nbrs δ, ∃ i, lv i = w := by
    intro w hw
    rcases hs29.nbrs_eq w hw with h | h | h
    · exact ⟨0, by rw [lv0, h]⟩
    · exact ⟨1, by rw [lv1, h]⟩
    · exact ⟨2, by rw [lv2, h]⟩
  have hV := isElemAbelian_Vn hA hb δ
  have hVc : ∀ a ∈ Vn δ, ∀ b ∈ Vn δ, a * b = b * a := fun a ha b hb' =>
    isElemAbelian_comm hV ha hb'
  have hVs : ∀ a ∈ Vn δ, a * a = 1 := fun a ha => by
    have := isElemAbelian_pow_eq_one hV ha
    simpa [pow_two] using this
  have hZV : Zv l ≤ Vn δ := Zv_le_Vn_nbrs hl
  have hCZ : ⁅Zv l, Qv δ⁆ ≤ Zv l := hs.comm_le_Zv hA h26 hδ hl
  have hYV : Yv δ ≤ Vn δ := (Yv_le_Zv hl).trans hZV
  have hnY := hs.stab_le_normalizer_Yv hA h26 hδ
  have hnV := stab_le_normalizer_Vn (H := H) (M := M) δ
  have hYc : ∀ x ∈ stab δ, ∀ y ∈ Yv δ, x * y * x⁻¹ ∈ Yv δ := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hnY hx) y).mp hy
  let u : Fin 2 → G := fun j => if j = 0 then u₀ else u₁
  have hu : ∀ j, u j ∈ Zv l := by
    intro j
    fin_cases j
    · exact hCZ h0
    · exact h1
  let w : Fin 3 × Fin 2 → G := fun p => d ^ (p.1 : ℕ) * u p.2 * (d ^ (p.1 : ℕ))⁻¹
  have hwV : ∀ p, w p ∈ Vn δ := fun p =>
    (Subgroup.mem_normalizer_iff.mp (hnV (hdδ p.1)) _).mp (hZV (hu p.2))
  obtain ⟨Φ, hΦV, hΦ⟩ := exists_Phi hVc hVs w hwV
  have hcomm : u₀ * u₁ = u₁ * u₀ := hVc _ (hZV (hCZ h0)) _ (hZV h1)
  have hdec := hs.Zv_decomp hA h26 hδ hl h0 h0' h1 h1' hcomm
  have hZconj : ∀ i : Fin 3, ∀ z ∈ Zv (lv i), (d ^ (i : ℕ))⁻¹ * z * d ^ (i : ℕ) ∈ Zv l := by
    intro i z hz
    have h := S29.Sit29.Zv_conj (g₀ ^ (i : ℕ)) l
    rw [hcoe] at h
    have hz' : z ∈ conjSub (d ^ (i : ℕ)) (Zv l) := by rw [h]; exact hz
    exact mem_conjSub.mp hz'
  have hZsub : ∀ i : Fin 3, ∀ z ∈ Zv (lv i),
      ∃ a b : Multiplicative (ZMod 2), ∃ y ∈ Yv δ, z = Φ (uel i a b) * y := by
    intro i z hz
    obtain ⟨a, b, y, hy, hz'⟩ := hdec _ (hZconj i z hz)
    refine ⟨a, b, d ^ (i : ℕ) * y * (d ^ (i : ℕ))⁻¹, hYc _ (hdδ _) y hy, ?_⟩
    rw [Phi_uel Φ w hΦ]
    have e1 : z = d ^ (i : ℕ) * ((d ^ (i : ℕ))⁻¹ * z * d ^ (i : ℕ)) * (d ^ (i : ℕ))⁻¹ := by group
    rw [e1, hz']
    have e2 : ∀ (c : Prop) [Decidable c] (x : G), d ^ (i : ℕ) * (if c then 1 else x) *
        (d ^ (i : ℕ))⁻¹ = if c then 1 else d ^ (i : ℕ) * x * (d ^ (i : ℕ))⁻¹ :=
      fun c _ x => conj_ite _ x c
    have e3 : d ^ (i : ℕ) * ((if a = 1 then 1 else u₀) * (if b = 1 then 1 else u₁) * y) *
        (d ^ (i : ℕ))⁻¹ = (d ^ (i : ℕ) * (if a = 1 then 1 else u₀) * (d ^ (i : ℕ))⁻¹) *
        (d ^ (i : ℕ) * (if b = 1 then 1 else u₁) * (d ^ (i : ℕ))⁻¹) *
        (d ^ (i : ℕ) * y * (d ^ (i : ℕ))⁻¹) := by group
    rw [e3, e2, e2]
    simp [w, u]
  let P : Pre6 (stab δ) (Vn δ) (Yv δ) := ⟨Φ, hΦV, hVc, hVs, hYV, hYc⟩
  have hgen : ∀ v ∈ Vn δ, ∃ f, ∃ y ∈ Yv δ, v = Φ f * y := by
    have hle : Vn δ ≤ P.Ψ ⊤ := by
      refine iSup₂_le fun m hm => ?_
      obtain ⟨i, rfl⟩ := lv_surj m hm
      intro z hz
      obtain ⟨a, b, y, hy, rfl⟩ := hZsub i z hz
      exact ⟨uel i a b, trivial, y, hy, rfl⟩
    intro v hv
    obtain ⟨f, -, y, hy, hvf⟩ := hle hv
    exact ⟨f, y, hy, hvf⟩
  let D : Dict6 (stab δ) (Vn δ) (Yv δ) := { P with gen := hgen }
  have hΦ' : ∀ p, D.Φ (mS p g1) = w p := hΦ
  have hwZ : ∀ (i : Fin 3) (j : Fin 2), w (i, j) ∈ Zv (lv i) := by
    intro i j
    have h := S29.Sit29.Zv_conj (g₀ ^ (i : ℕ)) l
    rw [hcoe] at h
    have hmem : w (i, j) ∈ conjSub (d ^ (i : ℕ)) (Zv l) := by
      rw [mem_conjSub]
      have e : (d ^ (i : ℕ))⁻¹ * w (i, j) * d ^ (i : ℕ) = u j := by simp only [w]; group
      rw [e]
      exact hu j
    rw [h] at hmem
    exact hmem
  have hZ : ∀ i : Fin 3, Zv (lv i) = D.Ψ (usub i) := by
    intro i
    apply le_antisymm
    · intro z hz
      obtain ⟨a, b, y, hy, hzz⟩ := hZsub i z hz
      exact ⟨uel i a b, uel_mem i a b, y, hy, hzz⟩
    · rintro _ ⟨f, hf, y, hy, rfl⟩
      obtain ⟨a, b, rfl⟩ := (mem_usub_iff i f).mp hf
      show Φ (uel i a b) * y ∈ Zv (lv i)
      rw [Phi_uel Φ w hΦ]
      refine (Zv (lv i)).mul_mem ((Zv (lv i)).mul_mem ?_ ?_) (Yv_le_Zv (lv_mem i) hy)
      · split_ifs
        · exact (Zv (lv i)).one_mem
        · exact hwZ i 0
      · split_ifs
        · exact (Zv (lv i)).one_mem
        · exact hwZ i 1
  have hYC : Yv δ ≤ ⁅Zv l, Qv δ⁆ := hs.Yv_le_comm hA h26 hδ hl
  have hinj : ∀ i, ∀ f ∈ usub i, f ∈ D.K → f = 1 := by
    intro i f hf hK
    obtain ⟨a, b, rfl⟩ := (mem_usub_iff i f).mp hf
    have hKy : D.Φ (uel i a b) ∈ Yv δ := hK
    rw [Phi_uel D.Φ w hΦ'] at hKy
    have e : (if a = 1 then 1 else w (i, 0)) * (if b = 1 then 1 else w (i, 1)) =
        d ^ (i : ℕ) * ((if a = 1 then 1 else u₀) * (if b = 1 then 1 else u₁)) *
          (d ^ (i : ℕ))⁻¹ := by
      split_ifs <;> simp [w, u]
    rw [e] at hKy
    have hq : (if a = 1 then 1 else u₀) * (if b = 1 then 1 else u₁) ∈ Yv δ := by
      have := hYc ((d ^ (i : ℕ))⁻¹) ((stab δ).inv_mem (hdδ i)) _ hKy
      simpa [mul_assoc] using this
    have hne : (g1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
    rcases mz_cases a with rfl | rfl <;> rcases mz_cases b with rfl | rfl
    · exact (uel_eq_one_iff i 1 1).mpr ⟨rfl, rfl⟩
    · exfalso
      simp [hne] at hq
      exact h1' (hYC hq)
    · exfalso
      simp [hne] at hq
      exact h0' hq
    · exfalso
      simp [hne] at hq
      apply h1'
      have : u₁ = u₀⁻¹ * (u₀ * u₁) := by group
      rw [this]
      exact ⁅Zv l, Qv δ⁆.mul_mem (⁅Zv l, Qv δ⁆.inv_mem h0) (hYC hq)
  have hZ' : ∀ i j : Fin 3, i ≠ j → D.Ψ (usub i) ⊓ D.Ψ (usub j) ≤ Yv δ := by
    intro i j hij
    rw [← hZ i, ← hZ j]
    exact (hs.inf_Zv_eq_Yv hA h26 hδ (lv_mem i) (lv_mem j) (lv_inj.ne hij)).le
  have hm := D.meet_of hinj hZ'
  have hperm : ∀ g : ↥(H ⊔ M), (g : G) ∈ stab δ → ∃ σ : Perm (Fin 3), ∀ i, g • lv i = lv (σ i) := by
    intro g hg
    have hex : ∀ i, ∃ j, lv j = g • lv i := fun i =>
      lv_surj _ (smul_mem_nbrs_of_mem_stab g hg (lv_mem i))
    choose f hf using hex
    have hinjf : Function.Injective f := by
      intro i j hij
      apply lv_inj
      have : g • lv i = g • lv j := by rw [← hf i, ← hf j, hij]
      exact smul_left_cancel g this
    have hbij := Finite.injective_iff_bijective.mp hinjf
    exact ⟨Equiv.ofBijective f hbij, fun i => by rw [Equiv.ofBijective_apply]; exact (hf i).symm⟩
  have hCy2 := (hs.relIndex_centralizer_Yv hA h26 hδ hl).1
  have hdCy : d ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := by
    have h := sq_mem_of_relIndex_two hCy2 hg0
    have e : d = (d * d) * (d * d) := by
      have h4 : d * d * (d * d) = d ^ 3 * d := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [h4, hd3, one_mul]
    rw [e]
    exact (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem h h
  have hdiCy : ∀ k : ℕ, d ^ k ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := fun k =>
    Subgroup.pow_mem _ hdCy k
  have hu0 : u 0 = u₀ := by simp [u]
  have hu1 : u 1 = u₁ := by simp [u]
  have hacts : ∀ (g : ↥(H ⊔ M)) (σ : Perm (Fin 3)), (g : G) ∈ stab δ →
      (∀ i, g • lv i = lv (σ i)) → D.Acts (g : G) σ (chi δ (g : G)) := by
    intro g σ hg hσ
    refine D.acts_of_basis fun p => ?_
    obtain ⟨i, j⟩ := p
    obtain ⟨x, hx⟩ : ∃ x : G, x = (g : G) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : G, c = d ^ ((σ i : Fin 3) : ℕ) := ⟨_, rfl⟩
    obtain ⟨h, hhdef⟩ : ∃ h : G, h = c⁻¹ * x * d ^ (i : ℕ) := ⟨_, rfl⟩
    rw [← hx] at hg ⊢
    have hcδ : c ∈ stab δ := hc ▸ hdδ _
    have hcCy : c ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := hc ▸ hdiCy _
    have hhE : h ∈ stab l ⊓ stab δ := by
      refine ⟨?_, ?_⟩
      · let h' : ↥(H ⊔ M) := (g₀ ^ ((σ i : Fin 3) : ℕ))⁻¹ * g * g₀ ^ (i : ℕ)
        have hh' : h' • l = l := by
          show ((g₀ ^ ((σ i : Fin 3) : ℕ))⁻¹ * g * g₀ ^ (i : ℕ)) • l = l
          rw [mul_smul, mul_smul]
          have h3 : g • (g₀ ^ (i : ℕ) • l) = g₀ ^ ((σ i : Fin 3) : ℕ) • l := hσ i
          rw [h3, inv_smul_smul]
        have h4 := mem_stab_of_smul_eq hh'
        have e : ((h' : ↥(H ⊔ M)) : G) = h := by
          rw [hhdef, hc, hx]
          simp [h', hcoe]
        rw [e] at h4
        exact h4
      · rw [hhdef]
        exact (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hcδ) hg) (hdδ _)
    have hCyiff : h ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) ↔
        x ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := by
      constructor
      · intro hh
        have e : x = c * h * (d ^ (i : ℕ))⁻¹ := by rw [hhdef]; group
        rw [e]
        exact (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem
          ((stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem hcCy hh)
          ((stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).inv_mem (hdiCy _))
      · intro hxC
        rw [hhdef]
        exact (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem
          ((stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem
            ((stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).inv_mem hcCy) hxC) (hdiCy _)
    have hedge := hs.edge_action hA h26 hb hδ hl h0 h0' h1 h1' hhE
    have hwk : ∀ j : Fin 2, w (σ i, j) = c * u j * c⁻¹ := fun j => by simp only [w]; rw [hc]
    have hwi : ∀ j : Fin 2, w (i, j) = d ^ (i : ℕ) * u j * (d ^ (i : ℕ))⁻¹ := fun j => rfl
    have hconj : ∀ j : Fin 2, x * w (i, j) * x⁻¹ = c * (h * u j * h⁻¹) * c⁻¹ := fun j => by
      rw [hwi, hhdef]; group
    fin_cases j
    · have hact : D.Φ (actE σ (chi δ x) (mS (i, 0) g1)) = w (σ i, 0) := by
        rw [actE_basis, map_mul, hΦ']
        simp
      show x * D.Φ (mS (i, 0) g1) * x⁻¹ * (D.Φ (actE σ (chi δ x) (mS (i, 0) g1)))⁻¹ ∈ Yv δ
      rw [hact, hΦ', hconj 0, hwk 0, hu0]
      have e : c * (h * u₀ * h⁻¹) * c⁻¹ * (c * u₀ * c⁻¹)⁻¹ = c * (h * u₀ * h⁻¹ * u₀⁻¹) * c⁻¹ := by
        group
      rw [e]
      exact hYc c hcδ _ hedge.1
    · show x * D.Φ (mS (i, 1) g1) * x⁻¹ * (D.Φ (actE σ (chi δ x) (mS (i, 1) g1)))⁻¹ ∈ Yv δ
      by_cases hxC : x ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)
      · have hhC := hCyiff.mpr hxC
        have hact : D.Φ (actE σ (chi δ x) (mS (i, 1) g1)) = w (σ i, 1) := by
          rw [actE_basis, chi_eq_false hxC, map_mul, hΦ']
          simp
        have hb1 := hedge.2
        simp only [hhC, ↓reduceIte, mul_one] at hb1
        rw [hact, hΦ', hconj 1, hwk 1, hu1]
        have e : c * (h * u₁ * h⁻¹) * c⁻¹ * (c * u₁ * c⁻¹)⁻¹ = c * (h * u₁ * h⁻¹ * u₁⁻¹) * c⁻¹ := by
          group
        rw [e]
        exact hYc c hcδ _ hb1
      · have hhC : h ∉ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := fun hh => hxC (hCyiff.mp hh)
        have hact : D.Φ (actE σ (chi δ x) (mS (i, 1) g1)) = w (σ i, 1) * w (σ i, 0) := by
          rw [actE_basis, chi_eq_true hxC, map_mul, hΦ']
          simp [hΦ']
        have hb1 := hedge.2
        simp only [hhC, ↓reduceIte] at hb1
        rw [hact, hΦ', hconj 1, hwk 1, hwk 0, hu1, hu0]
        have e : c * (h * u₁ * h⁻¹) * c⁻¹ * (c * u₁ * c⁻¹ * (c * u₀ * c⁻¹))⁻¹ =
            c * (h * u₁ * h⁻¹ * (u₁ * u₀)⁻¹) * c⁻¹ := by group
        rw [e]
        exact hYc c hcδ _ hb1
  have hrot : ∀ i : Fin 3, g₀ • lv i = lv (finRotate 3 i) := by
    intro i
    fin_cases i
    · show g₀ • (g₀ ^ 0 • l) = lv ((finRotate 3) 0)
      rw [show (finRotate 3) 0 = 1 by decide, lv1]
      simp
    · show g₀ • (g₀ ^ 1 • l) = lv ((finRotate 3) 1)
      rw [show (finRotate 3) 1 = 2 by decide, lv2]
      rw [pow_one, ← mul_smul, ← pow_two]
    · show g₀ • (g₀ ^ 2 • l) = lv ((finRotate 3) 2)
      rw [show (finRotate 3) 2 = 0 by decide, lv0, ← mul_smul, ← pow_succ', hg3, one_smul]
  have a1 : D.Acts (g₀ : G) (finRotate 3) false := by
    have := hacts g₀ (finRotate 3) hg0 hrot
    rwa [chi_eq_false hdCy] at this
  obtain ⟨s, hsQ, hsQ'⟩ := hs29.exists_q
  have hsl : s ∈ stab l := pCoreOf_le 2 _ hsQ
  have hsδ : s ∈ stab δ := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hl) hsQ
  have hsswap := hs29.smul_swap (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) hsl hsδ hsQ'
  have hsfix : (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) • l = l := smul_eq_of_mem_stab hsl
  have a2 : D.Acts s (swap 1 2) false := by
    have p0 : (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) • lv 0 = lv (swap 1 2 0) := by
      rw [show swap (1 : Fin 3) 2 0 = 0 by decide, lv0]
      exact hsfix
    have p1 : (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) • lv 1 = lv (swap 1 2 1) := by
      rw [show swap (1 : Fin 3) 2 1 = 2 by decide, lv2, lv1]
      exact hsswap.1
    have p2 : (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) • lv 2 = lv (swap 1 2 2) := by
      rw [show swap (1 : Fin 3) 2 2 = 1 by decide, lv1, lv2]
      exact hsswap.2
    have hp : ∀ i : Fin 3, (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) • lv i = lv (swap 1 2 i) := by
      intro i
      fin_cases i
      exacts [p0, p1, p2]
    have := hacts (⟨s, stab_le l hsl⟩ : ↥(H ⊔ M)) (swap 1 2) hsδ hp
    rwa [chi_eq_false (Qv_le_centralizer_Yv hA hl hsQ)] at this
  obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Qv δ, q ∉ Subgroup.centralizer (Yv δ : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hs.not_Qv_le_centralizer hA h26 hδ hl (fun x hx => hcon x hx)
  have hqδ : q ∈ stab δ := pCoreOf_le 2 _ hqQ
  have a3 : D.Acts q 1 true := by
    have hp : ∀ i : Fin 3, (⟨q, stab_le δ hqδ⟩ : ↥(H ⊔ M)) • lv i = lv ((1 : Perm (Fin 3)) i) := by
      intro i
      exact smul_eq_of_mem_stab (Qv_le_stab_of_mem_nbrs hA (lv_mem i) hqQ)
    have := hacts (⟨q, stab_le δ hqδ⟩ : ↥(H ⊔ M)) 1 hqδ hp
    rwa [chi_eq_true (fun h => hqC h.2)] at this
  obtain ⟨n, hn⟩ := D.exists_hasK hg0 hsδ hqδ a1 a2 a3 hm
  exact ⟨{
    D := D
    lv := lv
    lv0 := lv0
    lv_mem := lv_mem
    lv_inj := lv_inj
    lv_surj := lv_surj
    hZ := hZ
    n := n
    hn := hn
    perm_exists := hperm
    acts := hacts }⟩

theorem mem_centralizer_of_pow_three (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {d : G} (hd : d ∈ stab δ)
    (hd3 : d ^ 3 = 1) : d ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := by
  have h := sq_mem_of_relIndex_two (hs.relIndex_centralizer_Yv hA h26 hδ hl).1 hd
  have e : d = (d * d) * (d * d) := by
    have h4 : d * d * (d * d) = d ^ 3 * d := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4, hd3, one_mul]
  rw [e]
  exact (stab δ ⊓ Subgroup.centralizer (Yv δ : Set G)).mul_mem h h

theorem rot_data (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) (F : Frame δ l) {d : G} (hd : d ∈ stab δ)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ σ : Perm (Fin 3), σ ≠ 1 ∧ σ ^ 3 = 1 ∧ F.D.Acts d σ false := by
  obtain ⟨σ, hσ⟩ := F.perm_exists ⟨d, stab_le δ hd⟩ hd
  have hg3 : (⟨d, stab_le δ hd⟩ : ↥(H ⊔ M)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hpow : ∀ n : ℕ, ∀ i, (⟨d, stab_le δ hd⟩ : ↥(H ⊔ M)) ^ n • F.lv i = F.lv ((σ ^ n) i) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ', mul_smul, ih, hσ, pow_succ', Equiv.Perm.mul_apply]
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro h1
    apply smul_ne_self hA hl hd hd3 hd1
    have h2 : (⟨d, stab_le δ hd⟩ : ↥(H ⊔ M)) • F.lv 0 = F.lv 0 := by
      rw [hσ 0, h1]
      rfl
    rwa [F.lv0] at h2
  · refine Equiv.ext fun i => F.lv_inj ?_
    rw [← hpow 3 i, hg3, one_smul]
    rfl
  · have := F.acts ⟨d, stab_le δ hd⟩ σ hd hσ
    rwa [chi_eq_false (hs.mem_centralizer_of_pow_three hA h26 hδ hl hd hd3)] at this

theorem stab_data (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) (hl : l ∈ nbrs δ) (F : Frame δ l) {x : G}
    (hx : x ∈ stab l ⊓ stab δ) :
    ∃ σ : Perm (Fin 3), σ 0 = 0 ∧ (σ = 1 ↔ x ∈ Qv δ) ∧ F.D.Acts x σ (chi δ x) := by
  obtain ⟨σ, hσ⟩ := F.perm_exists ⟨x, stab_le δ hx.2⟩ hx.2
  refine ⟨σ, ?_, ⟨fun h1 => ?_, fun hq => ?_⟩, F.acts ⟨x, stab_le δ hx.2⟩ σ hx.2 hσ⟩
  · apply F.lv_inj
    have h1 := hσ 0
    rw [F.lv0] at h1
    rw [← h1, F.lv0]
    exact smul_eq_of_mem_stab hx.1
  · obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl
    refine h29.mem_Qv_of_fixes ⟨x, stab_le δ hx.2⟩ hx.2 fun w hw => ?_
    obtain ⟨i, rfl⟩ := F.lv_surj w hw
    rw [hσ i, h1]
    rfl
  · have hfix : ∀ i, (⟨x, stab_le δ hx.2⟩ : ↥(H ⊔ M)) • F.lv i = F.lv i := fun i =>
      smul_eq_of_mem_stab (Qv_le_stab_of_mem_nbrs hA (F.lv_mem i) hq)
    refine Equiv.ext fun i => F.lv_inj ?_
    rw [← hσ i]
    exact hfix i

theorem card_Vn_cases (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) :
    Nat.card (Vn δ) = 2 ^ 6 ∨ Nat.card (Vn δ) = 2 ^ 7 ∨ Nat.card (Vn δ) = 2 ^ 8 := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  have h := F.D.card_V_eq (hs.card_Yv hA h26 hδ) F.hn
  have hk := F.n.2
  rcases (by omega : F.n.val = 0 ∨ F.n.val = 1 ∨ F.n.val = 2) with h0 | h0 | h0
  · rw [h0] at h; exact Or.inr (Or.inr h)
  · rw [h0] at h; exact Or.inr (Or.inl h)
  · rw [h0] at h; exact Or.inl h

theorem centralizer_rot_iff (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) {d : G} (hd : d ∈ stab δ)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    Vn δ ⊓ Subgroup.centralizer ({d} : Set G) = Yv δ ↔ Nat.card (Vn δ) = 2 ^ 6 := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  obtain ⟨σ, hσ1, hσ3, hAct⟩ := hs.rot_data hA h26 hδ hl F hd hd3 hd1
  have hC := hs.mem_centralizer_of_pow_three hA h26 hδ hl hd hd3
  have hxY : ∀ y ∈ Yv δ, d * y * d⁻¹ = y := fun y hy => by
    rw [← Subgroup.mem_centralizer_iff.mp hC.2 y hy]; group
  exact (F.D.rot_fix hd hAct hσ1 hσ3 hd3 hxY F.hn).trans
    (F.D.card_V_eq_iff (hs.card_Yv hA h26 hδ) F.hn).symm

theorem comm_le_Zv_iff (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {x : G}
    (hx : x ∈ stab l ⊓ stab δ) (hxC : x ∈ Subgroup.centralizer (Yv δ : Set G))
    (hxQ : x ∉ Qv δ) :
    ⁅Vn δ, Subgroup.zpowers x⁆ ≤ Zv l ↔ Nat.card (Vn δ) = 2 ^ 6 := by
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  obtain ⟨σ, hσ0, hσQ, hAct⟩ := hs.stab_data hA h26 hδ hl F hx
  rw [chi_eq_false ⟨hx.2, hxC⟩] at hAct
  rw [F.Zv_eq]
  exact (F.D.stab_le_iff hx.2 hAct hσ0 (fun h => hxQ (hσQ.mp h)) F.hn).trans
    (F.D.card_V_eq_iff (hs.card_Yv hA h26 hδ) F.hn).symm

theorem comm_sup_Yv_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {x : G}
    (hx : x ∈ stab l ⊓ stab δ) (hxC : x ∈ Subgroup.centralizer (Yv δ : Set G))
    (hxQ : x ∉ Qv δ) (h4 : Nat.card (Vn δ) = 2 ^ 6) :
    ⁅Vn δ, Subgroup.zpowers x⁆ ⊔ Yv δ = Zv l := by
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  obtain ⟨σ, hσ0, hσQ, hAct⟩ := hs.stab_data hA h26 hδ hl F hx
  rw [chi_eq_false ⟨hx.2, hxC⟩] at hAct
  rw [F.Zv_eq]
  have h2 : F.n = 2 := (F.D.card_V_eq_iff (hs.card_Yv hA h26 hδ) F.hn).mp h4
  exact F.D.stab_sup_eq hx.2 hAct hσ0 (fun h => hxQ (hσQ.mp h)) F.hn h2

theorem not_comm_le_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {x : G}
    (hx : x ∈ stab l ⊓ stab δ) (hxC : x ∉ Subgroup.centralizer (Yv δ : Set G)) :
    ¬ ⁅Vn δ, Subgroup.zpowers x⁆ ≤ Zv l := by
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  obtain ⟨σ, hσ0, hσQ, hAct⟩ := hs.stab_data hA h26 hδ hl F hx
  rw [chi_eq_true (fun h => hxC h.2)] at hAct
  rw [F.Zv_eq]
  exact F.D.stab_not_le hx.2 hAct hσ0 F.hn

theorem comm_Qv_le_Zv_iff (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) :
    ⁅Vn δ, Qv l⁆ ≤ Zv l ↔ Nat.card (Vn δ) = 2 ^ 6 := by
  have hQl : Qv l ≤ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) := Qv_le_centralizer_Yv hA hl
  have hQs : Qv l ≤ stab l := pCoreOf_le 2 _
  constructor
  · intro h
    obtain ⟨a₂, a₃, h29⟩ := hs.exists_sit29 hA h26 hδ hl
    obtain ⟨s, hsQ, hsQ'⟩ := h29.exists_q
    have hs1 : ⁅Vn δ, Subgroup.zpowers s⁆ ≤ Zv l :=
      (Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hsQ)).trans h
    exact (hs.comm_le_Zv_iff hA h26 hb hδ hl ⟨hQs hsQ, (hQl hsQ).1⟩ (hQl hsQ).2 hsQ').mp hs1
  · intro h4
    rw [Subgroup.commutator_le]
    intro v hv x hx
    by_cases hxQ : x ∈ Qv δ
    · have hxst : x ∈ Qst δ := Qv_inf_Qv_le_Qst hA hl ⟨hx, hxQ⟩
      have := Subgroup.commutator_mem_commutator hv hxst
      rw [hs.comm_Vn_Qst hA h26 hδ hl] at this
      exact Yv_le_Zv hl this
    · have hle := (hs.comm_le_Zv_iff hA h26 hb hδ hl ⟨hQs hx, (hQl hx).1⟩ (hQl hx).2 hxQ).mpr h4
      exact hle (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x))

theorem Zv_sup_Zv_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {m : Geo H M}
    (hm : m ∈ nbrs δ) (hlm : l ≠ m) (h4 : Nat.card (Vn δ) = 2 ^ 6) :
    Zv l ⊔ Zv m = Vn δ := by
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  obtain ⟨i, hi⟩ := F.lv_surj m hm
  have h2 : F.n = 2 := (F.D.card_V_eq_iff (hs.card_Yv hA h26 hδ) F.hn).mp h4
  have hn : F.D.HasK 2 := by rw [← h2]; exact F.hn
  have hi0 : (0 : Fin 3) ≠ i := fun h => hlm (by rw [← F.lv0, h, hi])
  rw [F.Zv_eq, ← hi, F.hZ i]
  exact F.D.pair_sup hn hi0

theorem Vst_frame (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ)
    (h4 : Nat.card (Vn δ) = 2 ^ 6) :
    ∃ F : Frame δ l, F.D.HasK 2 ∧ ⁅Vn δ, Qv δ⁆ = F.D.Ψ (rg 1 true) := by
  obtain ⟨F⟩ := hs.exists_frame hA h26 hb hδ hl
  have h2 : F.n = 2 := (F.D.card_V_eq_iff (hs.card_Yv hA h26 hδ) F.hn).mp h4
  have hn : F.D.HasK 2 := by rw [← h2]; exact F.hn
  obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Qv δ, q ∉ Subgroup.centralizer (Yv δ : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hs.not_Qv_le_centralizer hA h26 hδ hl (fun x hx => hcon x hx)
  have hqδ : q ∈ stab δ := pCoreOf_le 2 _ hqQ
  have hQb : ∀ b ∈ Qv δ, b ∈ stab δ ∧ ∃ e, F.D.Acts b 1 e := by
    intro b hb'
    have hbδ : b ∈ stab δ := pCoreOf_le 2 _ hb'
    exact ⟨hbδ, chi δ b, F.acts ⟨b, stab_le δ hbδ⟩ 1 hbδ fun i =>
      smul_eq_of_mem_stab (Qv_le_stab_of_mem_nbrs hA (F.lv_mem i) hb')⟩
  have hAq : F.D.Acts q 1 true := by
    have := F.acts ⟨q, stab_le δ hqδ⟩ 1 hqδ fun i =>
      smul_eq_of_mem_stab (Qv_le_stab_of_mem_nbrs hA (F.lv_mem i) hqQ)
    rwa [chi_eq_true (fun h => hqC h.2)] at this
  have hYQ : Yv δ ≤ ⁅Vn δ, Qv δ⁆ := by
    rw [← hs.comm_Vn_Qst hA h26 hδ hl]
    exact Subgroup.commutator_mono le_rfl inf_le_left
  exact ⟨F, hn, F.D.comm_eq_rg hQb hqQ hAq hYQ⟩

theorem card_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (h4 : Nat.card (Vn δ) = 2 ^ 6) :
    Nat.card (Vst δ) = 2 ^ 4 := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  obtain ⟨F, hn, heq⟩ := hs.Vst_frame hA h26 hb hδ hl h4
  show Nat.card ↥⁅Vn δ, Qv δ⁆ = 2 ^ 4
  rw [heq, F.D.card_Ψ_rg_one (hs.card_Yv hA h26 hδ) hn]
  norm_num

theorem Vst_inf_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hδ : vtype δ = true) (hl : l ∈ nbrs δ)
    (h4 : Nat.card (Vn δ) = 2 ^ 6) : Vst δ ⊓ Zv l = ⁅Zv l, Qv δ⁆ := by
  obtain ⟨F, hn, heq⟩ := hs.Vst_frame hA h26 hb hδ hl h4
  have hle : ⁅Zv l, Qv δ⁆ ≤ Vst δ ⊓ Zv l :=
    le_inf (Subgroup.commutator_mono (Zv_le_Vn_nbrs hl) le_rfl) (hs.comm_le_Zv hA h26 hδ hl)
  have hcard : Nat.card ↥(Vst δ ⊓ Zv l) = 8 := by
    have e1 : Vst δ ⊓ Zv l = F.D.Ψ (rg 1 true) ⊓ F.D.Ψ (usub 0) := by
      rw [← F.Zv_eq, ← heq]
      rfl
    rw [e1]
    exact F.D.card_Ψ_rg_one_inter (hs.card_Yv hA h26 hδ) hn
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hs.card_comm_Qv hA h26 hδ hl])).symm

theorem Yv_le_Vst (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : vtype δ = true) : Yv δ ≤ Vst δ := by
  obtain ⟨l, hl⟩ := exists_adj_of_vtype_true hA hδ
  rw [← hs.comm_Vn_Qst hA h26 hδ hl]
  exact Subgroup.commutator_mono le_rfl inf_le_left

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
