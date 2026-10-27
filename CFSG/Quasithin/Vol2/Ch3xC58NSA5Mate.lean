module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCPf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCFin
public import CFSG.Quasithin.Background.C58IndexTwo

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58
  CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure A5Cfg (L R S : Subgroup G) (P : A5Pi L) : Prop where
  short : IsShort2 L
  alt : IsAltType L 5
  SR : S ≤ R
  RS : R ≤ normalizer (S : Set G)
  SN : S ≤ normalizer (L : Set G)
  US : blockU L ≤ S
  QD : S ⊓ centralizer (blockU L : Set G) = blockU L ⊔ (S ⊓ centralizer (L : Set G))
  SE : P.im S = Estd
  syl : IsSylowTwoOf (R ⊓ L) L
  perm : ∀ g ∈ R, g ∉ normalizer (L : Set G) → ∀ a ∈ L, ∀ b ∈ conjSubgroup L g, a * b = b * a

@[expose] def IsTv (S : Subgroup G) (g : G) : Prop :=
  ∃ c : G, ∀ z ∈ S ⊓ centralizer (S : Set G),
    z⁻¹ * (g * z * g⁻¹) = 1 ∨ z⁻¹ * (g * z * g⁻¹) = c

omit [Finite G] in
theorem IsTv.conj {S : Subgroup G} {g y : G} (hy : y ∈ normalizer (S : Set G))
    (h : IsTv S g) : IsTv S (y * g * y⁻¹) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨y * c * y⁻¹, fun z hz => ?_⟩
  have hy' : y⁻¹ ∈ normalizer ((S ⊓ centralizer (S : Set G) : Subgroup G) : Set G) :=
    inv_mem (mem_normalizer_inf hy (mem_normalizer_centralizer hy))
  have hz' : y⁻¹ * z * y ∈ S ⊓ centralizer (S : Set G) := by
    have := (mem_normalizer_iff.mp hy' z).mp hz
    simpa using this
  have e : z⁻¹ * (y * g * y⁻¹ * z * (y * g * y⁻¹)⁻¹) =
      y * ((y⁻¹ * z * y)⁻¹ * (g * (y⁻¹ * z * y) * g⁻¹)) * y⁻¹ := by group
  rcases hc _ hz' with h | h
  · left; rw [e, h]; group
  · right; rw [e, h]

omit [Finite G] in
theorem card_sylow_alternating_five (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card P = 4 := by
  have h60' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide +kernel
  rw [Sylow.card_eq_multiplicity, h60']
  have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h60, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

namespace A5Cfg

variable {L R S : Subgroup G} {P : A5Pi L} (hc : A5Cfg L R S P)
include hc

omit [Finite G] in
theorem U_le_L : blockU L ≤ L := (C1.blockU_le_blockQ hc.short).trans (C1.blockQ_le L)

omit [Finite G] in
theorem U_comm {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L) : a * b = b * a :=
  C1.blockU_comm hc.short a ha b (C1.blockU_le_blockQ hc.short hb)

omit [Finite G] in
theorem U_sq {u : G} (hu : u ∈ blockU L) : u ^ 2 = 1 := C1.blockU_sq hc.short u hu

omit [Finite G] in
theorem U_inv {u : G} (hu : u ∈ blockU L) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc.U_sq hu)

theorem eq_one_of_mem {u : G} (hu : u ∈ blockU L) (hu' : u ∈ centralizer (L : Set G)) :
    u = 1 := by
  have h : u ∈ blockZ L := ⟨hu, hu'⟩
  rw [AppC.blockZ_eq_bot_of_alt5 hc.short hc.alt] at h
  exact h

omit [Finite G] in
theorem S_le_NU : S ≤ normalizer (blockU L : Set G) := fun _ hs =>
  C1.mem_normalizer_blockU (hc.SN hs)

omit [Finite G] in
theorem DU {u d : G} (hu : u ∈ blockU L) (hd : d ∈ S ⊓ centralizer (L : Set G)) :
    u * d = d * u :=
  mem_centralizer_iff.mp hd.2 u (hc.U_le_L hu)

omit [Finite G] in
theorem S_le_ND : S ≤ normalizer ((S ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_inf (Subgroup.le_normalizer hs) (mem_normalizer_centralizer (hc.SN hs))

omit [Finite G] in
theorem U_le_Q : blockU L ≤ S ⊓ centralizer (blockU L : Set G) :=
  le_inf hc.US fun _ hu => mem_centralizer_iff.mpr fun _ hv => hc.U_comm hv hu

omit [Finite G] in
theorem D_le_Q : S ⊓ centralizer (L : Set G) ≤ S ⊓ centralizer (blockU L : Set G) :=
  inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hc.U_le_L))

omit [Finite G] in
theorem D_eq : S ⊓ centralizer (L : Set G) =
    (S ⊓ centralizer (blockU L : Set G)) ⊓ centralizer (L : Set G) :=
  le_antisymm (le_inf hc.D_le_Q inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

omit [Finite G] hc in
theorem pf_eq_one {y : G} (hyN : y ∈ normalizer (L : Set G))
    (hyC : y ∈ centralizer (blockU L : Set G)) : P.pf y = 1 := by
  rw [P.pf_eq hyN, P.hker]
  intro u hu
  have := mem_centralizer_iff.mp hyC u hu
  calc y * u * y⁻¹ = u * y * y⁻¹ := by rw [this]
    _ = u := by group

omit [Finite G] hc in
theorem mem_centralizer_of_pf {y : G} (hyN : y ∈ normalizer (L : Set G)) (h : P.pf y = 1) :
    y ∈ centralizer (blockU L : Set G) := by
  rw [P.pf_eq hyN] at h
  have h2 := (P.hker ⟨y, hyN⟩).1 h
  rw [mem_centralizer_iff]
  intro u hu
  have h3 : y * u * y⁻¹ = u := h2 u hu
  calc u * y = (y * u * y⁻¹) * y := by rw [h3]
    _ = y * u := by group

omit [Finite G] in
theorem V_le_S {x : G} (hx : x ∈ normalizer (S : Set G)) : conjSubgroup (blockU L) x ≤ S := by
  have := conjSubgroup_mono hc.US x
  rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hx] at this

omit [Finite G] in
theorem V_le_N {x : G} (hx : x ∈ normalizer (S : Set G)) :
    conjSubgroup (blockU L) x ≤ normalizer (L : Set G) := (hc.V_le_S hx).trans hc.SN

omit [Finite G] in
theorem V_elem (x : G) : IsElemAbelian 2 (conjSubgroup (blockU L) x) :=
  isElemAbelian_two_iff.mpr ((C1.elemAb2_blockU hc.short).conjSubgroup x)

omit [Finite G] in
theorem V_comm {x v v' : G} (hv : v ∈ conjSubgroup (blockU L) x)
    (hv' : v' ∈ conjSubgroup (blockU L) x) : v * v' = v' * v :=
  ((C1.elemAb2_blockU hc.short).conjSubgroup x).1 v hv v' hv'

omit [Finite G] in
theorem S_le_NV {x : G} (hx : x ∈ normalizer (S : Set G)) :
    S ≤ normalizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
  have := conjSubgroup_mono hc.S_le_NU x
  rwa [conjSubgroup_eq_iff_mem_normalizer.mpr hx, conjSubgroup_normalizer] at this

omit [Finite G] in
theorem im_V_le {x : G} (hx : x ∈ normalizer (S : Set G)) :
    P.im (conjSubgroup (blockU L) x) ≤ Estd := by
  rw [← hc.SE]; exact P.im_mono (hc.V_le_S hx)

theorem key_count {x : G} (hx : x ∈ normalizer (S : Set G)) :
    Nat.card (P.im (conjSubgroup (blockU L) x)) *
      Nat.card (FixΔ (P.im (conjSubgroup (blockU L) x⁻¹))) = 16 := by
  have h4 := P.card_im_mul (hc.V_le_N hx)
  have h5 := P.card_fix (hc.V_le_N (inv_mem hx))
  have hU : conjSubgroup (conjSubgroup (blockU L) x) x⁻¹ = blockU L :=
    conjSubgroup_conjSubgroup_inv (blockU L) x
  have e : Nat.card ↥(conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G)) =
      Nat.card ↥(blockU L ⊓ centralizer (conjSubgroup (blockU L) x⁻¹ : Set G)) := by
    rw [← card_conjSubgroup (conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G)) x⁻¹,
      conjSubgroup_inf, conjSubgroup_centralizer, hU]
  rw [e, h5, card_conjSubgroup, P.card_blockU] at h4
  exact h4

omit [Finite G] hc in
theorem not_le_inv {x : G}
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) :
    ¬ conjSubgroup (blockU L) x⁻¹ ≤ centralizer (blockU L : Set G) := by
  intro h
  apply hxU
  have h1 := conjSubgroup_mono h x
  rw [conjSubgroup_inv_conjSubgroup, conjSubgroup_centralizer, le_centralizer_iff] at h1
  exact h1

theorem isTv_of_mem {s₀ : G} (hs₀L : s₀ ∈ L) (hD : P.pf s₀ ∈ Dset) (hE : P.pf s₀ ∉ Eset) :
    IsTv S s₀ := by
  classical
  have hs₀N : s₀ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hs₀L
  have hz0 : isEven z0 := by decide +kernel
  obtain ⟨cstar, hcstarU, hcstar⟩ := P.bf_surj ⟨z0, (mem_evenWeight_iff _).2 hz0⟩
  refine ⟨cstar, fun z hz => ?_⟩
  have hzQ : z ∈ S ⊓ centralizer (blockU L : Set G) :=
    ⟨hz.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hc.US) hz.2⟩
  rw [hc.QD] at hzQ
  obtain ⟨u, hu, d, hd, rfl⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hzQ
  have huS : ∀ s ∈ S, s * u * s⁻¹ = u := by
    intro s hs
    have hzc : s * (u * d) = u * d * s := (mem_centralizer_iff.mp hz.2) s hs
    have hw : u⁻¹ * (s * u * s⁻¹) = d * (s * d⁻¹ * s⁻¹) := by
      calc u⁻¹ * (s * u * s⁻¹) = u⁻¹ * (s * (u * d)) * s⁻¹ * (s * d⁻¹ * s⁻¹) := by group
        _ = u⁻¹ * (u * d * s) * s⁻¹ * (s * d⁻¹ * s⁻¹) := by rw [hzc]
        _ = d * (s * d⁻¹ * s⁻¹) := by group
    have hwU : u⁻¹ * (s * u * s⁻¹) ∈ blockU L :=
      mul_mem (inv_mem hu) ((mem_normalizer_iff.mp (hc.S_le_NU hs) u).mp hu)
    have hwD : d * (s * d⁻¹ * s⁻¹) ∈ centralizer (L : Set G) :=
      mul_mem hd.2 ((mem_normalizer_iff.mp (mem_normalizer_centralizer (hc.SN hs)) _).mp
        (inv_mem hd.2))
    rw [← hw] at hwD
    have h1 := hc.eq_one_of_mem hwU hwD
    calc s * u * s⁻¹ = u * (u⁻¹ * (s * u * s⁻¹)) := by group
      _ = u := by rw [h1, mul_one]
  have hds : s₀ * d = d * s₀ := mem_centralizer_iff.mp hd.2 s₀ hs₀L
  set c : G := u⁻¹ * (s₀ * u * s₀⁻¹) with hcdef
  have hcU : c ∈ blockU L := mul_mem (inv_mem hu) (PiData.conj_mem_U hs₀N hu)
  have hcd : c * d = d * c := hc.DU hcU hd
  have hval : (u * d)⁻¹ * (s₀ * (u * d) * s₀⁻¹) = c := by
    have e1 : (u * d)⁻¹ * (s₀ * (u * d) * s₀⁻¹) = d⁻¹ * c * (s₀ * d * s₀⁻¹) := by
      rw [hcdef]; group
    rw [e1, hds]
    calc d⁻¹ * c * (d * s₀ * s₀⁻¹) = d⁻¹ * (c * d) := by group
      _ = c := by rw [hcd]; group
  rw [hval]
  have hwfix : ∀ σ ∈ Eset, pact σ (P.bf u).1 = (P.bf u).1 := by
    intro σ hσ
    have hσS : σ ∈ P.im S := by rw [hc.SE]; exact (mem_Estd σ).2 hσ
    obtain ⟨y, hy, rfl⟩ := (P.mem_im_pf hc.SN).1 hσS
    have hyu : y * u = u * y := by
      have := huS y hy
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [this]
    exact congrArg Subtype.val ((P.comm_iff (hc.SN hy) hu).1 hyu)
  have hbfc : P.bf c = P.bf u + vact (P.pf s₀) (P.bf u) := by
    rw [hcdef, P.bf_mul (inv_mem hu) (PiData.conj_mem_U hs₀N hu), P.bf_conj hs₀N hu, hc.U_inv hu]
  have hwe : isEven (P.bf u).1 := (mem_evenWeight_iff _).1 (P.bf u).2
  rcases AppCS2.phi_two (P.pf s₀) hD hE (P.bf u).1 hwe hwfix with h | h
  · left
    have : P.bf c = P.bf 1 := by
      rw [P.bf_one, hbfc]
      apply Subtype.ext
      simpa [vact, add_comm] using h
    exact P.bf_inj hcU (one_mem _) this
  · right
    have : P.bf c = P.bf cstar := by
      rw [hcstar, hbfc]
      apply Subtype.ext
      simpa [vact, add_comm] using h
    exact P.bf_inj hcU hcstarU this

theorem not_isTv {g : G} (hgR : g ∈ R) (hg : g ∉ normalizer (L : Set G)) : ¬ IsTv S g := by
  rintro ⟨c, hcv⟩
  set F₁ : Subgroup G := blockU L ⊓ centralizer (S : Set G) with hF₁
  have hcardF : Nat.card ↥F₁ = 4 := by
    rw [hF₁, P.card_fix hc.SN, hc.SE, card_fix_Estd]
  have hg'N : g⁻¹ ∉ normalizer (L : Set G) := fun h => hg (by simpa using inv_mem h)
  have hperm := hc.perm g⁻¹ (inv_mem hgR) hg'N
  let ψ : ↥F₁ → ↥({1, c} : Set G) := fun f =>
    ⟨(f : G)⁻¹ * (g * f * g⁻¹), by
      rcases hcv f ⟨hc.US f.2.1, f.2.2⟩ with h | h
      · left; exact h
      · right; exact h⟩
  have hinj : Function.Injective ψ := by
    intro f f' h
    have h1 : (f : G)⁻¹ * (g * f * g⁻¹) = (f' : G)⁻¹ * (g * f' * g⁻¹) := congrArg Subtype.val h
    have hwU : (f' : G) * (f : G)⁻¹ ∈ blockU L := mul_mem f'.2.1 (inv_mem f.2.1)
    have hgw : g * ((f' : G) * (f : G)⁻¹) * g⁻¹ = (f' : G) * (f : G)⁻¹ := by
      calc g * ((f' : G) * (f : G)⁻¹) * g⁻¹ =
            (f' : G) * (((f' : G)⁻¹ * (g * f' * g⁻¹)) * ((f : G)⁻¹ * (g * f * g⁻¹))⁻¹) *
              (f : G)⁻¹ := by group
        _ = (f' : G) * (((f : G)⁻¹ * (g * f * g⁻¹)) * ((f : G)⁻¹ * (g * f * g⁻¹))⁻¹) *
              (f : G)⁻¹ := by rw [← h1]
        _ = (f' : G) * (f : G)⁻¹ := by group
    have hgw' : g⁻¹ * ((f' : G) * (f : G)⁻¹) * g = (f' : G) * (f : G)⁻¹ := by
      calc g⁻¹ * ((f' : G) * (f : G)⁻¹) * g =
            g⁻¹ * (g * ((f' : G) * (f : G)⁻¹) * g⁻¹) * g := by rw [hgw]
        _ = (f' : G) * (f : G)⁻¹ := by group
    have hwL : (f' : G) * (f : G)⁻¹ ∈ conjSubgroup L g⁻¹ := by
      rw [mem_conjSubgroup_iff, inv_inv, hgw']
      exact hc.U_le_L hwU
    have hwC : (f' : G) * (f : G)⁻¹ ∈ centralizer (L : Set G) :=
      mem_centralizer_iff.mpr fun a ha => hperm a ha _ hwL
    have h3 := hc.eq_one_of_mem hwU hwC
    exact Subtype.ext (mul_inv_eq_one.mp h3).symm
  have hle := Nat.card_le_card_of_injective ψ hinj
  have h2 : Nat.card ↥({1, c} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({1, c} : Set G).ncard ≤ ({c} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem conj_swapper_mem {x s₀ : G} (hxR : x ∈ normalizer (R : Set G))
    (hxS : x ∈ normalizer (S : Set G)) (hs₀R : s₀ ∈ R) (hs₀L : s₀ ∈ L) (hD : P.pf s₀ ∈ Dset)
    (hE : P.pf s₀ ∉ Eset) : x * s₀ * x⁻¹ ∈ normalizer (L : Set G) := by
  by_contra h
  exact hc.not_isTv ((mem_normalizer_iff.mp hxR s₀).mp hs₀R) h
    ((hc.isTv_of_mem hs₀L hD hE).conj hxS)

omit [Finite G] hc in
theorem mem_normalizer_V {L : Subgroup G} {x s : G} (h : x * s * x⁻¹ ∈ normalizer (L : Set G)) :
    s ∈ normalizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
  have e : x * s = (x * s * x⁻¹) * x := by group
  rw [e, ← conjSubgroup_conjSubgroup,
    conjSubgroup_eq_iff_mem_normalizer.mpr (C1.mem_normalizer_blockU h)]

theorem exists_swapper : ∃ s₀ ∈ R, s₀ ∈ L ∧ P.pf s₀ ∈ Dset ∧ P.pf s₀ ∉ Eset := by
  classical
  have hSyl := hc.syl
  have hK₀2 : IsPGroup 2 ((R ⊓ L).subgroupOf L) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  let Pp : Sylow 2 ↥L := hK₀2.toSylow hSyl.2.2
  have hcard := card_sylow_alternating_five (Pp.mapSurjective P.hα)
  have hcoe : ((Pp.mapSurjective P.hα : Sylow 2 (alternatingGroup (Fin 5))) :
      Subgroup (alternatingGroup (Fin 5))) = ((R ⊓ L).subgroupOf L).map P.α := by
    rw [Sylow.coe_mapSurjective]
    rfl
  set K : Subgroup (Perm (Fin 5)) :=
    (((R ⊓ L).subgroupOf L).map P.α).map (alternatingGroup (Fin 5)).subtype with hKdef
  have hKcard : Nat.card K = 4 := by
    rw [hKdef, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective,
      ← hcoe]
    exact hcard
  have hev : ∀ g ∈ K, Perm.sign g = 1 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact Equiv.Perm.mem_alternatingGroup.1 a.2
  obtain ⟨g, hgK, hgE⟩ := AppCS2.exists_not_mem_Eset K hev (by omega)
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hgK
  obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 ha
  have hℓ' : (ℓ : G) ∈ R ⊓ L := Subgroup.mem_subgroupOf.1 hℓ
  have hℓN : (ℓ : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer ℓ.2
  have hpf : P.pf (ℓ : G) = ((P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
    rw [P.pf_eq hℓN]
    exact P.hπα (ℓ : G) ℓ.2
  have hD : P.pf (ℓ : G) ∈ Dset := by
    rw [mem_Dset]
    intro σ hσ
    have hσS : σ ∈ P.im S := by rw [hc.SE]; exact (mem_Estd σ).2 hσ
    obtain ⟨y, hy, rfl⟩ := (P.mem_im_pf hc.SN).1 hσS
    have hℓS : (ℓ : G) ∈ normalizer (S : Set G) := hc.RS hℓ'.1
    have hyc : (ℓ : G) * y * (ℓ : G)⁻¹ ∈ S := (mem_normalizer_iff.mp hℓS y).mp hy
    have h1 : P.pf ((ℓ : G) * y * (ℓ : G)⁻¹) ∈ P.im S := (P.mem_im_pf hc.SN).2 ⟨_, hyc, rfl⟩
    rw [hc.SE, P.pf_mul (mul_mem hℓN (hc.SN hy)) (inv_mem hℓN), P.pf_mul hℓN (hc.SN hy),
      P.pf_inv hℓN] at h1
    exact (mem_Estd _).1 h1
  refine ⟨ℓ, hℓ'.1, ℓ.2, hD, ?_⟩
  rw [hpf]
  exact hgE

theorem im_V_eq {x : G} (hxS : x ∈ normalizer (S : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) :
    P.im (conjSubgroup (blockU L) x) = Estd := by
  classical
  obtain ⟨s₀, hs₀R, hs₀L, hD, hE⟩ := hc.exists_swapper
  set V := conjSubgroup (blockU L) x with hV
  have hVN : V ≤ normalizer (L : Set G) := hc.V_le_N hxS
  have hWne : P.im V ≠ ⊥ := by
    intro hbot
    apply hxU
    intro v hv
    rw [mem_centralizer_iff]
    intro u hu
    have h1 : P.π ⟨v, hVN hv⟩ = 1 := by
      have : P.π ⟨v, hVN hv⟩ ∈ P.im V := P.pi_mem_im hv
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have h2 : v * u * v⁻¹ = u := (P.hker ⟨v, hVN hv⟩).1 h1 u hu
    calc u * v = (v * u * v⁻¹) * v := by rw [h2]
      _ = v * u := by group
  have hel := P.im_elemAbelian (hc.V_elem x)
  have hel' := P.im_elemAbelian (hc.V_elem x⁻¹)
  obtain ⟨a, haW, b, hbW, hW4, hWcard, hWfix⟩ := exists_four_card (P.im V) hel.1 hel.2
  obtain ⟨a', ha'W, b', hb'W, hW'4, hW'card, hW'fix⟩ :=
    exists_four_card (P.im (conjSubgroup (blockU L) x⁻¹)) hel'.1 hel'.2
  have hEset : ∀ g ∈ P.im V, g ∈ Eset := fun g hg => (mem_Estd g).1 (hc.im_V_le hxS hg)
  have hE' : ∀ g ∈ P.im (conjSubgroup (blockU L) x⁻¹), g ∈ Eset := fun g hg =>
    (mem_Estd g).1 (hc.im_V_le (inv_mem hxS) hg)
  have hc1 := hc.key_count hxS
  have hc2 := hc.key_count (inv_mem hxS)
  rw [inv_inv] at hc2
  have hs₀V := mem_normalizer_V (hc.conj_swapper_mem hxR hxS hs₀R hs₀L hD hE)
  have hs₀N : s₀ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hs₀L
  have hdW : ∀ g ∈ P.im V, P.pf s₀ * g * (P.pf s₀)⁻¹ ∈ P.im V := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := (P.mem_im_pf hVN).1 hg
    have hv' : s₀ * v * s₀⁻¹ ∈ V := (mem_normalizer_iff.mp hs₀V v).mp hv
    rw [← P.pf_inv hs₀N, ← P.pf_mul hs₀N (hVN hv), ← P.pf_mul (mul_mem hs₀N (hVN hv))
      (inv_mem hs₀N)]
    exact (P.mem_im_pf hVN).2 ⟨_, hv', rfl⟩
  have hK := AppCS2.K_fin a (hEset a haW) b (hEset b hbW) a' (hE' a' ha'W) b' (hE' b' hb'W)
    (P.pf s₀) hD
  have hWfourEq : four a b = Eset := by
    apply hK hE
    · intro g hg
      exact (hW4 _).1 (hdW g ((hW4 g).2 hg))
    · intro h1
      apply hWne
      rw [eq_bot_iff]
      intro g hg
      have := (hW4 g).1 hg
      rw [h1] at this
      exact Subgroup.mem_bot.2 (Finset.mem_singleton.1 this)
    · rw [← hWcard, ← hW'fix]; exact hc1
    · rw [← hW'card, ← hWfix]; exact hc2
  ext g
  rw [hW4 g, hWfourEq, mem_Estd]

theorem cent_U_V {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) :
    blockU L ⊓ centralizer (conjSubgroup (blockU L) x : Set G) ≤
        ⁅conjSubgroup (blockU L) x, blockU L⁆ ∧
      blockU L ⊓ centralizer (conjSubgroup (blockU L) x : Set G) =
        blockU L ⊓ conjSubgroup (blockU L) x ∧
      blockU L ⊓ conjSubgroup (blockU L) x =
        conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G) := by
  have hVN : conjSubgroup (blockU L) x ≤ normalizer (L : Set G) := hc.V_le_N hx
  have hcard1 : Nat.card ↥(blockU L ⊓ centralizer (conjSubgroup (blockU L) x : Set G)) = 4 := by
    rw [P.card_fix hVN, hVE, card_fix_Estd]
  have hcard2 : Nat.card ↥(conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G)) = 4 := by
    have h4 := P.card_im_mul hVN
    rw [hVE, Estd_card, card_conjSubgroup, P.card_blockU] at h4
    omega
  have h1 : blockU L ⊓ centralizer (conjSubgroup (blockU L) x : Set G) ≤
      ⁅conjSubgroup (blockU L) x, blockU L⁆ := by
    intro u hu
    obtain ⟨huU, huC⟩ := hu
    set f : evenWeight 5 := Multiplicative.toAdd (P.β ⟨u, huU⟩) with hf
    have hfix : f ∈ FixΔ Estd := by
      rw [← hVE]
      intro σ hσ
      obtain ⟨y, hy, rfl⟩ := (P.mem_im).1 hσ
      have hcy := Subgroup.mem_centralizer_iff.1 huC y hy
      have h := P.hcomp y ⟨u, huU⟩ ⟨u, huU⟩ (by
        show u = (y : G) * u * (y : G)⁻¹
        rw [hcy]; group)
      exact h.symm
    have hfe : isEven f.1 := (mem_evenWeight_iff f.1).1 f.2
    have hfE : ∀ σ ∈ Eset, pact σ f.1 = f.1 := fun σ hσ =>
      congrArg Subtype.val (hfix σ ((mem_Estd σ).2 hσ))
    obtain ⟨t', htE, w, hwe, hw⟩ := fix_comm f.1 hfe hfE
    have htV : t' ∈ P.im (conjSubgroup (blockU L) x) := by
      rw [hVE]; exact (mem_Estd t').2 htE
    obtain ⟨v, hvV, hvt⟩ := (P.mem_im).1 htV
    have hw' : w ∈ evenWeight 5 := (mem_evenWeight_iff w).2 hwe
    set u' : ↥(blockU L) := P.β.symm (Multiplicative.ofAdd ⟨w, hw'⟩) with hu'
    have hu'β : Multiplicative.toAdd (P.β u') = ⟨w, hw'⟩ := by simp [hu']
    have hvU' : (v : G) * (u' : G) * (v : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) v.2) u').mp u'.2
    have hcomp := P.hcomp v u' ⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ rfl
    have heq : (⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ : ↥(blockU L)) * u'⁻¹ = ⟨u, huU⟩ := by
      apply P.β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hcomp, hvt, hu'β]
      apply Subtype.ext
      funext i
      have hi := congrFun hw i
      simp only [Pi.add_apply] at hi
      show pact t' w i + -(w i) = f.1 i
      rw [← hi]
      generalize pact t' w i = a
      generalize w i = b
      revert a b
      decide
    have hu : u = (v : G) * (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ := by
      have := congrArg Subtype.val heq
      simpa using this.symm
    rw [hu]
    exact Subgroup.commutator_mem_commutator hvV u'.2
  have h2 : blockU L ⊓ conjSubgroup (blockU L) x ≤
      conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G) := by
    intro u hu
    exact ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun u' hu' => hc.U_comm hu' hu.1⟩
  have hh1 : blockU L ⊓ centralizer (conjSubgroup (blockU L) x : Set G) ≤
      blockU L ⊓ conjSubgroup (blockU L) x := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have := h1 hu
    have hcV : ⁅conjSubgroup (blockU L) x, blockU L⁆ ≤ conjSubgroup (blockU L) x := by
      rw [Subgroup.commutator_le]
      intro v hv u' hu'
      have e : ⁅v, u'⁆ = v * (u' * v⁻¹ * u'⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem hv ((Subgroup.mem_normalizer_iff.1 (hc.S_le_NV hx (hc.US hu')) v⁻¹).1
        (inv_mem hv))
    exact hcV this
  have e1 := Subgroup.eq_of_le_of_card_ge hh1
    (by rw [hcard1]; exact (Subgroup.card_le_of_le h2).trans hcard2.le)
  have e2 := Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard2, ← e1, hcard1])
  exact ⟨h1, e1, e2⟩

theorem D_le_centralizer_V {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) :
    S ⊓ centralizer (L : Set G) ≤ centralizer (conjSubgroup (blockU L) x : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvS : v ∈ S := hc.V_le_S hx hv
  have hcV : d * v * d⁻¹ * v⁻¹ ∈ conjSubgroup (blockU L) x :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 (hc.S_le_NV hx hd.1) v).1 hv) (inv_mem hv)
  have hcD : d * v * d⁻¹ * v⁻¹ ∈ S ⊓ centralizer (L : Set G) := by
    have h1 : v * d⁻¹ * v⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
      (Subgroup.mem_normalizer_iff.1 (hc.S_le_ND hvS) d⁻¹).1 (inv_mem hd)
    have e : d * v * d⁻¹ * v⁻¹ = d * (v * d⁻¹ * v⁻¹) := by group
    rw [e]
    exact mul_mem hd h1
  have hmem : d * v * d⁻¹ * v⁻¹ ∈
      conjSubgroup (blockU L) x ⊓ centralizer (blockU L : Set G) :=
    ⟨hcV, Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subgroup.mem_centralizer_iff.1 hcD.2 u (hc.U_le_L hu)⟩
  rw [← (hc.cent_U_V hx hVE).2.2] at hmem
  have h1 := hc.eq_one_of_mem hmem.1 hcD.2
  have h2 : d * v * d⁻¹ = v := mul_inv_eq_one.mp h1
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem exists_mem_V_mul_Q {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) {b : G} (hb : b ∈ S) :
    ∃ v ∈ conjSubgroup (blockU L) x, v⁻¹ * b ∈ S ⊓ centralizer (blockU L : Set G) := by
  have hbN : b ∈ normalizer (L : Set G) := hc.SN hb
  have hπ : P.pf b ∈ P.im (conjSubgroup (blockU L) x) := by
    rw [hVE, ← hc.SE]
    exact (P.mem_im_pf hc.SN).2 ⟨b, hb, rfl⟩
  obtain ⟨v, hv, hvπ⟩ := (P.mem_im_pf (hc.V_le_N hx)).1 hπ
  have hvN : v ∈ normalizer (L : Set G) := hc.V_le_N hx hv
  refine ⟨v, hv, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hc.V_le_S hx hv)) hb,
    mem_centralizer_of_pf (P := P) (mul_mem (inv_mem hvN) hbN) ?_⟩⟩
  rw [P.pf_mul (inv_mem hvN) hbN, P.pf_inv hvN, hvπ, inv_mul_cancel]

theorem sup_V_Q {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) :
    conjSubgroup (blockU L) x ⊔ (S ⊓ centralizer (blockU L : Set G)) = S := by
  apply le_antisymm (sup_le (hc.V_le_S hx) inf_le_left)
  intro b hb
  obtain ⟨v, hv, hq⟩ := hc.exists_mem_V_mul_Q hx hVE hb
  have e : b = v * (v⁻¹ * b) := by group
  rw [e]
  exact mul_mem (mem_sup_left hv) (mem_sup_right hq)

omit [Finite G] hc in
theorem conj_sqSub_of {Q : Subgroup G} {x : G} (e1 : sqSub Q = sqSub (Q ⊓ conjSubgroup Q x))
    (e2 : sqSub Q = sqSub (Q ⊓ conjSubgroup Q x⁻¹)) : conjSubgroup (sqSub Q) x = sqSub Q := by
  calc conjSubgroup (sqSub Q) x = conjSubgroup (sqSub (Q ⊓ conjSubgroup Q x⁻¹)) x := by
        rw [← e2]
    _ = sqSub (conjSubgroup (Q ⊓ conjSubgroup Q x⁻¹) x) := conjSubgroup_sqSub _ _
    _ = sqSub (Q ⊓ conjSubgroup Q x) := by
        rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
          inf_comm (conjSubgroup Q x) Q]
    _ = sqSub Q := e1.symm

omit [Finite G] hc in
theorem sqSub_eq_inf_of {U Q D Q' : Subgroup G} (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hQ : Q = U ⊔ D)
    (hUQ : U ≤ Q) (hDQ : D ≤ Q') (hQc : Q ≤ centralizer (U : Set G)) :
    sqSub Q = sqSub (Q ⊓ Q') := by
  have e : Q = U ⊔ (Q ⊓ Q') := by
    apply le_antisymm
    · calc Q = U ⊔ D := hQ
        _ ≤ U ⊔ (Q ⊓ Q') := sup_le_sup_left (le_inf (le_sup_right.trans hQ.symm.le) hDQ) _
    · exact sup_le hUQ inf_le_left
  calc sqSub Q = sqSub (U ⊔ (Q ⊓ Q')) := congrArg sqSub e
    _ = sqSub (Q ⊓ Q') := sqSub_sup_eq hU2 fun u hu a ha =>
        mem_centralizer_iff.mp (hQc ha.1) u hu

theorem mem_normalizer_sqSub {x : G} (hxS : x ∈ normalizer (S : Set G))
    (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) :
    x ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  have hU2 : ∀ u ∈ blockU L, u ^ 2 = 1 := fun u hu => hc.U_sq hu
  have hDc : ∀ u ∈ blockU L, ∀ a ∈ S ⊓ centralizer (L : Set G), u * a = a * u :=
    fun u hu a ha => hc.DU hu ha
  have hQ : sqSub (S ⊓ centralizer (L : Set G)) = sqSub (S ⊓ centralizer (blockU L : Set G)) := by
    rw [hc.QD, sqSub_sup_eq hU2 hDc]
  have hVE := hc.im_V_eq hxS hxR hxU
  have hVE' := hc.im_V_eq (inv_mem hxS) (inv_mem hxR) (not_le_inv hxU)
  have hDy : ∀ y : G, y ∈ normalizer (S : Set G) → P.im (conjSubgroup (blockU L) y) = Estd →
      S ⊓ centralizer (L : Set G) ≤ conjSubgroup (S ⊓ centralizer (blockU L : Set G)) y := by
    intro y hyS hyE
    rw [conjSubgroup_inf, conjSubgroup_centralizer, conjSubgroup_eq_self hyS]
    exact le_inf inf_le_left (hc.D_le_centralizer_V hyS hyE)
  have e1 := sqSub_eq_inf_of hU2 hc.QD hc.U_le_Q (hDy x hxS hVE) inf_le_right
  have e2 := sqSub_eq_inf_of hU2 hc.QD hc.U_le_Q (hDy x⁻¹ (inv_mem hxS) hVE') inf_le_right
  have h := conj_sqSub_of e1 e2
  rw [← hQ] at h
  exact conjSubgroup_eq_iff_mem_normalizer.mp h

end A5Cfg

end CFSG.Quasithin.C58NS
