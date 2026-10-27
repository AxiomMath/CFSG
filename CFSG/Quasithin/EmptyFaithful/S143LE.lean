module

public import CFSG.Quasithin.EmptyFaithful.S143LD
public import CFSG.Quasithin.EmptyFaithful.S143LF
public import CFSG.Quasithin.EmptyFaithful.S143JA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section DFacts

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1)

omit hS in
theorem dOf_le_normalizer_Ac :
    dOf T M ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := fun _ hd =>
  c.normal_Ac hrW hrV hr2 (Subgroup.mem_sup_right (Subgroup.mem_inf.mp hd).1)

include hS

theorem D_cmat {d : G} (hd : d ∈ dOf T M) :
    cmat z a r r1 d = I4 ∨ cmat z a r r1 d = Tz := by
  have hB := hS.basis
  have hdC : d ∈ Subgroup.centralizer (uOfL22 T M : Set G) := (Subgroup.mem_inf.mp hd).2
  have hzU : z ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.z_V
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.a_V
  have hrU : r ∈ uOfL22 T M := hrW.1
  have hconj : ∀ e ∈ uOfL22 T M, d * e * d⁻¹ = e := fun e he => by
    have h := Subgroup.mem_centralizer_iff.mp hdC e he
    rw [← h]; group
  have h1R : r1 ∈ rOf T M := c.Ac_le_rOf hrW hrV hr2 hS.r1_A
  have hcomm := c.dOf_commutator_mem hd h1R
  have hr1A := hS.r1_A
  have hzA := hS.z_A
  have hm : cmat z a r r1 d = (⟨coordsOf z a r r1 (d * z * d⁻¹), coordsOf z a r r1 (d * a * d⁻¹),
    coordsOf z a r r1 (d * r * d⁻¹), coordsOf z a r r1 (d * r1 * d⁻¹)⟩ : Mat4) := rfl
  rw [hm, hconj z hzU, hconj a haU, hconj r hrU]
  rcases c.mem_Z_cases hS.z_mem hS.z_ne hcomm with h | h
  · left
    have : d * r1 * d⁻¹ = r1 := by
      have e : d * r1 * d⁻¹ = (d * r1 * d⁻¹ * r1⁻¹) * r1 := by group
      rw [e, h, one_mul]
    rw [this, hB.coordsOf_e0, hB.coordsOf_e1, hB.coordsOf_e2, hB.coordsOf_e3]
    rfl
  · right
    have : d * r1 * d⁻¹ = z * r1 := by
      have e : d * r1 * d⁻¹ = (d * r1 * d⁻¹ * r1⁻¹) * r1 := by group
      rw [e, h]
    rw [this, hB.coordsOf_mul hzA hr1A, hB.coordsOf_e0, hB.coordsOf_e1, hB.coordsOf_e2,
      hB.coordsOf_e3]
    rfl

theorem D0_index_le :
    ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)).index ≤ 2 := by
  have hB := hS.basis
  by_cases htop : (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) = ⊤
  · rw [htop, Subgroup.index_top]
    omega
  · obtain ⟨a', ha'⟩ : ∃ a' : ↥(dOf T M),
        a' ∉ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) := by
      by_contra hh
      push Not at hh
      exact htop (eq_top_iff.mpr fun x _ => hh x)
    have hdN := dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2)
    have ha'T : cmat z a r r1 (a' : G) = Tz := by
      rcases D_cmat hS a'.2 with h | h
      · exfalso
        exact ha' (Subgroup.mem_subgroupOf.mpr
          ((hB.cmat_eq_one_iff_mem_centralizer (hdN a'.2)).mp h))
      · exact h
    have hidx : ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨a', ha', fun b => ?_⟩
      rcases D_cmat hS b.2 with h | h
      · right
        exact Subgroup.mem_subgroupOf.mpr ((hB.cmat_eq_one_iff_mem_centralizer (hdN b.2)).mp h)
      · left
        refine Subgroup.mem_subgroupOf.mpr ((hB.cmat_eq_one_iff_mem_centralizer
          (Subgroup.mul_mem _ (hdN b.2) (hdN a'.2))).mp ?_)
        show cmat z a r r1 ((b : G) * (a' : G)) = I4
        rw [hB.cmat_mul (hdN b.2) (hdN a'.2), ha'T, h, Tz_sq]
    omega

omit hS in
theorem D_inf_Ac_le_Z {d : G} (hd : d ∈ dOf T M) (hdA : d ∈ c.Ac hrW hrV hr2) :
    d ∈ quasithinOmegaOneCenter T := by
  have hdU : d ∈ uOfL22 T M :=
    c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2 ⟨hdA, (Subgroup.mem_inf.mp hd).1⟩
  have h : d ∈ centerOf (uOfL22 T M) := ⟨hdU, (Subgroup.mem_inf.mp hd).2⟩
  rwa [c.centerOf_uOfL22_eq] at h

omit hS in
theorem Z_le_dOf (c : Counter T M g) : quasithinOmegaOneCenter T ≤ dOf T M := fun u hu => by
  have h1 : u ∈ centerOf (uOfL22 T M) := c.h1281.omegaOneCenter_le_centerOf_uOfL22 hu
  exact Subgroup.mem_inf.mpr ⟨uOfL22_le_qOf c h1.1, h1.2⟩

variable {t : G} (htT : t ∈ T) (htRQ : t ∉ rOf T M ⊔ qOf T) {y : G} {cm : Mat4}
  (hM : KModel hS cm y)

include htT htRQ hM

theorem D_inf_kOf_le_Ac {Vl : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)}
    (hconf : Conf6 cm Vl s) {d : G} (hd : d ∈ dOf T M)
    (hdK : d ∈ kOf T M (c.Ac hrW hrV hr2)) : d ∈ c.Ac hrW hrV hr2 := by
  have hB := hS.basis
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  rcases D_cmat hS hd with h | h
  · have hC := (hB.cmat_eq_one_iff_mem_centralizer hdN).mp h
    exact hS.kOf_inf_centralizer_le htT htRQ hM ⟨hdK, hC⟩
  · exfalso
    have hσ : ∀ w, n6Act (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)) (psi cm w) =
        n6Act s (psi cm w) := by
      intro w
      rw [hM.q_act, h]
      exact (psi_intertwine hconf.s_eq w).symm
    have hact : ∀ b : N6, n6Act (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)) b = n6Act s b := fun b => by
      obtain ⟨w, rfl⟩ := psi_surjective hM.inj b
      exact hσ w
    have hsσ : (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6))⁻¹ * s = 1 := by
      apply n6_faithful_perm
      intro b
      rw [map_mul, MulAut.mul_apply, ← hact b, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
        map_one]
      rfl
    have hsig : (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)).sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2
    have hs_eq : (hM.q ⟨d, hdK⟩ : Equiv.Perm (Fin 6)) = s := inv_mul_eq_one.mp hsσ
    rw [hs_eq, hconf.s_sign] at hsig
    exact absurd hsig (by decide)

variable {Vl : List (Equiv.Perm (Fin 6))} {s : Equiv.Perm (Fin 6)}
  (hconf : Conf6 cm Vl s)
  (hVl : ∀ σ ∈ Vl, ∃ u ∈ uOfL22 T M, mm cm (matOf6 σ) = mm (cmat z a r r1 u) cm)

include hconf hVl

theorem vanL_of_cocyc {δ : G} (hδD : δ ∈ dOf T M)
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) {w : Fin 6 → ZMod 2}
    (hw : ∀ σ : ↥(alternatingGroup (Fin 6)), cocyc hM δ σ = dW w σ.1) : VanL Vl w := by
  intro σ hσ
  obtain ⟨u, hu, hmat⟩ := hVl σ hσ
  have huK : u ∈ kOf T M (c.Ac hrW hrV hr2) :=
    c.rOf_sup_uOfL22_le_kOf hrW hrV hr2 (Subgroup.mem_sup_right hu)
  have hcu : u * δ = δ * u := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδD).2 u hu
  have h1 := cocyc_eq_one_of_centralizes htT htRQ hM hδ huK hcu
  have hσ1 : σ.sign = 1 := hconf.sign_V σ hσ
  have hq : (hM.q ⟨u, huK⟩ : Equiv.Perm (Fin 6)) = σ := by
    refine perm_eq_of_act hM.inj (Equiv.Perm.mem_alternatingGroup.mp (hM.q _).2) hσ1 fun w' => ?_
    rw [hM.q_act]
    exact (psi_intertwine hmat w').symm
  have h2 : cocyc hM δ ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ1⟩ = 1 := by
    have : hM.q ⟨u, huK⟩ = ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ1⟩ := Subtype.ext hq
    rw [← this]
    exact h1
  rw [hw] at h2
  exact (dW_eq_one_iff w σ).mp h2

variable (hC1 : ∀ γ : G, (∀ k ∈ kOf T M (c.Ac hrW hrV hr2), k * γ = γ * k) → γ = 1)

include hC1

theorem D0_card_le :
    Nat.card ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)) ≤ 4 := by
  classical
  let S : Finset (Equiv.Perm (Fin 6) → (Fin 6 → ZMod 2)) :=
    (Finset.univ.filter (VanL Vl)).image Fw
  have hS4 : S.card ≤ 4 := hconf.m1
  have hex : ∀ δ : ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)),
      ∃ w : Fin 6 → ZMod 2, ∀ σ : ↥(alternatingGroup (Fin 6)),
        cocyc hM ((δ : ↥(dOf T M)) : G) σ = dW w σ.1 := fun δ =>
    eq_dW htT htRQ hM (Subgroup.mem_subgroupOf.mp δ.2)
  choose w hw using hex
  let F : ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)) → ↥S :=
    fun δ => ⟨Fw (w δ), Finset.mem_image.mpr ⟨w δ, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      vanL_of_cocyc hS htT htRQ hM hconf hVl (δ : ↥(dOf T M)).2 (Subgroup.mem_subgroupOf.mp δ.2) (hw δ)⟩,
      rfl⟩⟩
  have hF : Function.Injective F := by
    intro δ δ' hδ
    have h1 : Fw (w δ) = Fw (w δ') := congrArg Subtype.val hδ
    have h2 : cocyc hM ((δ : ↥(dOf T M)) : G) = cocyc hM ((δ' : ↥(dOf T M)) : G) := by
      funext σ
      have h3 := congrFun h1 σ.1
      have hs1 : σ.1.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp σ.2
      simp only [Fw, hs1, ite_true] at h3
      rw [hw δ σ, hw δ' σ]
      unfold dW
      congr 1
    have h4 := cocyc_injective htT htRQ hC1 hM (Subgroup.mem_subgroupOf.mp δ.2)
      (Subgroup.mem_subgroupOf.mp δ'.2) h2
    exact Subtype.ext (Subtype.ext h4)
  calc Nat.card ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M))
      ≤ Nat.card ↥S := Nat.card_le_card_of_injective F hF
    _ = S.card := by simp
    _ ≤ 4 := hS4

theorem D_noncomm {d δ : G} (hd : d ∈ dOf T M) (hdT : cmat z a r r1 d = Tz) (hδD : δ ∈ dOf T M)
    (hδ : δ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) (hδA : δ ∉ c.Ac hrW hrV hr2) :
    d * δ * d⁻¹ ≠ δ := by
  intro hcomm
  have hdN : d ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd
  have hdKN := c.dOf_le_normalizer_kOf hrW hrV hr2 hd
  have hdK : ∀ k ∈ kOf T M (c.Ac hrW hrV hr2), d * k * d⁻¹ ∈ kOf T M (c.Ac hrW hrV hr2) :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp hdKN k).mp hk
  have hdδ : d * δ = δ * d := by
    calc d * δ = (d * δ * d⁻¹) * d := by group
      _ = δ * d := by rw [hcomm]
  obtain ⟨w, hw⟩ := eq_dW htT htRQ hM hδ
  have hVan := vanL_of_cocyc hS htT htRQ hM hconf hVl hδD hδ hw
  have hs2 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hconf.s_sq
  have hEqui : EquiS s w := by
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.mpr hσ
    have hmem : s * σ * s ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, hσ, hconf.s_sign]
      decide)
    have h := cocyc_conj htT htRQ hM hδ hdN hdK hdT hconf.s_sign hconf.s_eq hdδ ⟨σ, hσA⟩ hmem
    rw [hw ⟨s * σ * s, hmem⟩, hw ⟨σ, hσA⟩] at h
    have h' := congrArg (fun b : N6 => Multiplicative.toAdd b.1) h
    rw [hs2]
    funext i
    exact congrFun h' i
  obtain ⟨b, hb⟩ := dW_principal_of_even (hconf.m2 w hVan hEqui)
  exact hδA (mem_Ac_of_principal htT htRQ hC1 hM hδ b (fun σ => by rw [hw, hb]))

theorem dihedral_main
    (hN : Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G) =
      kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M) :
    (∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) ∧
      (Nonempty (↥(dOf T M) ≃* DihedralGroup 4) ↔
        ((kOf T M (c.Ac hrW hrV hr2)).relIndex
            (Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G)) = 4 ∧
          c.Ac hrW hrV hr2 < Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G))) := by
  classical
  have hB := hS.basis
  have hKN := c.kOf_le_normalizer_Ac hrW hrV hr2
  have hDN := dOf_le_normalizer_Ac (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2)
  have hDKN := c.dOf_le_normalizer_kOf hrW hrV hr2
  have hD0 := D0_card_le hS htT htRQ hM hconf hVl hC1
  have hidx := D0_index_le hS
  have hzU : z ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M hS.z_V
  have hzD : z ∈ dOf T M := Z_le_dOf c hS.z_mem
  let zD : ↥(dOf T M) := ⟨z, hzD⟩
  have hz2 : zD * zD = 1 := Subtype.ext (c.sq_Ac hrW hrV hr2 hS.z_A)
  have hz1 : zD ≠ 1 := fun h => hS.z_ne (congrArg Subtype.val h)
  have hzc : ∀ x : ↥(dOf T M), x * zD = zD * x := fun x => Subtype.ext (by
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 z hzU
    exact h.symm)
  have hzD₀ : zD ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun a' ha' =>
      hB.comm a' ha' z hS.z_A)
  have hnorm : ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (by
      have h1 := centralizer_conj_mem (hDN g.2) (Subgroup.mem_subgroupOf.mp hn)
      exact h1)⟩
  have hsq : ∀ x ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M),
      x * x = 1 := by
    intro x hx
    have hxΓ : (x : G) ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    show (x : G) * (x : G) = 1
    apply cocyc_injective htT htRQ hC1 hM (Subgroup.mul_mem _ hxΓ hxΓ) (Subgroup.one_mem _)
    funext σ
    rw [cocyc_mul htT htRQ hM hxΓ hxΓ, n6_mul_self]
    obtain ⟨k, rfl⟩ := hM.q_surjective σ
    rw [cocyc_q htT htRQ hM (Subgroup.one_mem _), fcoc_one hB]
  have hcomm : ∀ x ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M),
      ∀ y ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M),
        x * y = y * x := by
    intro x hx y hy
    have hxΓ : (x : G) ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      Subgroup.mem_subgroupOf.mp hx
    have hyΓ : (y : G) ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
      Subgroup.mem_subgroupOf.mp hy
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    apply cocyc_injective htT htRQ hC1 hM (Subgroup.mul_mem _ hxΓ hyΓ) (Subgroup.mul_mem _ hyΓ hxΓ)
    funext σ
    rw [cocyc_mul htT htRQ hM hxΓ hyΓ, cocyc_mul htT htRQ hM hyΓ hxΓ, mul_comm]
  have hnc : Nat.card ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)) = 4 →
      ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)).index = 2 →
        ∃ d δ : ↥(dOf T M),
          δ ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) ∧
            d * δ * d⁻¹ ≠ δ := by
    intro h4 hi2
    obtain ⟨δ, hδ, hδA⟩ : ∃ δ : ↥(dOf T M),
        δ ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) ∧
          (δ : G) ∉ c.Ac hrW hrV hr2 := by
      by_contra hh
      push Not at hh
      have hle : (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) ≤
          (quasithinOmegaOneCenter T).subgroupOf (dOf T M) := fun x hx =>
        D_inf_Ac_le_Z (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) x.2 (hh x hx)
      have h1 := Subgroup.card_le_of_le hle
      have h2 : Nat.card ↥((quasithinOmegaOneCenter T).subgroupOf (dOf T M)) = 2 := by
        rw [← c.h1281.card_omegaOneCenter]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_dOf c)).toEquiv
      omega
    obtain ⟨d, hd⟩ : ∃ d : ↥(dOf T M),
        d ∉ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) := by
      by_contra hh
      push Not at hh
      have : ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)) = ⊤ :=
        eq_top_iff.mpr fun x _ => hh x
      rw [this, Subgroup.index_top] at hi2
      omega
    have hdT : cmat z a r r1 (d : G) = Tz := by
      rcases D_cmat hS d.2 with h | h
      · exfalso
        exact hd (Subgroup.mem_subgroupOf.mpr
          ((hB.cmat_eq_one_iff_mem_centralizer (hDN d.2)).mp h))
      · exact h
    refine ⟨d, δ, hδ, fun h => ?_⟩
    exact D_noncomm hS htT htRQ hM hconf hVl hC1 d.2 hdT δ.2 (Subgroup.mem_subgroupOf.mp hδ) hδA
      (congrArg Subtype.val h)
  obtain ⟨hemb, h8⟩ := exists_embedding_dihedral_of_structure hz2 hz1 hzc _ hzD₀ hsq hcomm hD0 hidx hnc
  refine ⟨hemb, ?_⟩
  have hKD : kOf T M (c.Ac hrW hrV hr2) ⊓ dOf T M = quasithinOmegaOneCenter T := by
    apply le_antisymm
    · intro d hd
      exact D_inf_Ac_le_Z (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) hd.2
        (D_inf_kOf_le_Ac hS htT htRQ hM hconf hd.2 hd.1)
    · intro u hu
      have huA : u ∈ c.Ac hrW hrV hr2 :=
        c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hu)
      exact ⟨((c.Ac_le_rOf hrW hrV hr2).trans (le_sup_left.trans
        (c.rOf_sup_uOfL22_le_kOf hrW hrV hr2))) huA, Z_le_dOf c hu⟩
  have hrel : (kOf T M (c.Ac hrW hrV hr2)).relIndex
      (Subgroup.normalizer (kOf T M (c.Ac hrW hrV hr2) : Set G)) * 2 = Nat.card (dOf T M) := by
    rw [hN]
    have h1 := Subgroup.relIndex_mul_card (H := kOf T M (c.Ac hrW hrV hr2))
      (K := kOf T M (c.Ac hrW hrV hr2) ⊔ dOf T M)
    rw [inf_eq_left.mpr le_sup_left] at h1
    have h2 := card_sup_mul_card_inf_of_le_normalizer hDKN
    rw [hKD, c.h1281.card_omegaOneCenter] at h2
    have hKpos : 0 < Nat.card ↥(kOf T M (c.Ac hrW hrV hr2)) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hKpos
    rw [← h2, ← h1]
    ring
  constructor
  · rintro ⟨e⟩
    have hD8 : Nat.card ↥(dOf T M) = 8 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    refine ⟨by omega, ?_⟩
    obtain ⟨δ, hδ, hδA⟩ : ∃ δ : ↥(dOf T M),
        δ ∈ (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) ∧
          (δ : G) ∉ c.Ac hrW hrV hr2 := by
      by_contra hh
      push Not at hh
      have hle : (Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M) ≤
          (quasithinOmegaOneCenter T).subgroupOf (dOf T M) := fun x hx =>
        D_inf_Ac_le_Z (c := c) (hrW := hrW) (hrV := hrV) (hr2 := hr2) x.2 (hh x hx)
      have h1 := Subgroup.card_le_of_le hle
      have h2 : Nat.card ↥((quasithinOmegaOneCenter T).subgroupOf (dOf T M)) = 2 := by
        rw [← c.h1281.card_omegaOneCenter]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_dOf c)).toEquiv
      have h3 := Subgroup.card_mul_index
        ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M))
      have h4 : Nat.card ↥((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)) *
          ((Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)).subgroupOf (dOf T M)).index ≤ 2 * 2 :=
        Nat.mul_le_mul (h1.trans (le_of_eq h2)) hidx
      omega
    refine lt_of_le_of_ne (fun a' ha' => Subgroup.mem_centralizer_iff.mpr fun a'' ha'' =>
      hB.comm a'' ha'' a' ha') (fun heq => hδA ?_)
    rw [heq]
    exact Subgroup.mem_subgroupOf.mp hδ
  · rintro ⟨hrel4, -⟩
    exact h8 (by omega)

end DFacts

end S143

end CFSG.Quasithin
