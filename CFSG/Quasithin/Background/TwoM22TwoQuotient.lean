module

public import CFSG.Quasithin.Background.TwoM22TwoOuter

public section

namespace CFSG.GroupTheory

open Subgroup

theorem mul_comm_of_isPerfect_of_commutator_mem {G : Type*} [Group G] {C Y : Subgroup G}
    (hperf : Group.IsPerfect ↥C) (hYc : ∀ y ∈ Y, ∀ c ∈ C, y * c = c * y)
    {g : G} (hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hcomm : ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ Y) :
    ∀ c ∈ C, g * c = c * g := by
  let ψ : ↥C →* ↥(C ⊓ Y) :=
    { toFun := fun c =>
        ⟨g * (c : G) * g⁻¹ * (c : G)⁻¹,
          C.mul_mem (hgC c c.2) (C.inv_mem c.2), hcomm c c.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro c₁ c₂
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hB : (c₁ : G)⁻¹ * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹)
            = (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹ := by
          have h := hYc _ (hcomm c₂ c₂.2) (c₁ : G) c₁.2
          calc (c₁ : G)⁻¹ * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹)
              = (c₁ : G)⁻¹ * ((g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) * c₁) * (c₁ : G)⁻¹ := by
                group
            _ = (c₁ : G)⁻¹ * (c₁ * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹)) * (c₁ : G)⁻¹ := by
                rw [h]
            _ = (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹ := by group
        calc g * ((c₁ : G) * (c₂ : G)) * g⁻¹ * ((c₁ : G) * (c₂ : G))⁻¹
            = (g * (c₁ : G) * g⁻¹) * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹ := by
              group
          _ = (g * (c₁ : G) * g⁻¹) * ((g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) * (c₁ : G)⁻¹) := by
              group
          _ = (g * (c₁ : G) * g⁻¹) * ((c₁ : G)⁻¹ * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹)) := by
              rw [hB]
          _ = (g * (c₁ : G) * g⁻¹ * (c₁ : G)⁻¹) * (g * (c₂ : G) * g⁻¹ * (c₂ : G)⁻¹) := by
              group }
  have hψ : ψ = 1 := by
    rw [← MonoidHom.ker_eq_top_iff, eq_top_iff, ← hperf.commutator_eq_top]
    change ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ ψ.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (hYc (ψ a).1 (ψ a).2.2 (ψ b).1 (ψ b).2.1))
  intro c hc
  have h1 : g * c * g⁻¹ * c⁻¹ = 1 := by
    have h2 : ψ ⟨c, hc⟩ = 1 := by rw [hψ]; rfl
    have hval : (ψ ⟨c, hc⟩).val = g * c * g⁻¹ * c⁻¹ := rfl
    rw [h2] at hval
    simpa using hval.symm
  have h3 : g * c * g⁻¹ = c := mul_inv_eq_one.mp h1
  calc g * c = (g * c * g⁻¹) * g := by group
    _ = c * g := by rw [h3]

theorem exists_lift_ker_eq_center_of_isPerfect_of_ker_le
    {C D M : Type*} [Group C] [Group D] [Group M] (hC : Group.IsPerfect C)
    (q : C →* M) (hq : Function.Surjective q) (hkerq : q.ker ≤ Subgroup.center C)
    (hM : Subgroup.center M = ⊥) (φ : C →* D) (hφ : Function.Surjective φ)
    (hYq : φ.ker ≤ q.ker) (hcard : Nat.card q.ker = 6) (hcardY : Nat.card φ.ker = 3) :
    ∃ qbar : D →* M, Function.Surjective qbar ∧ qbar.ker = Subgroup.center D ∧
      Nat.card (Subgroup.center D) = 2 := by
  have hkerq' : q.ker = Subgroup.center C := by
    have h := CFSG.LocalCores.comap_center_eq_of_perfect hC q hq hkerq
    rw [hM] at h
    rw [← h]
    ext x
    simp [Subgroup.mem_comap, MonoidHom.mem_ker]
  have hcomapφ : Subgroup.comap φ (Subgroup.center D) = Subgroup.center C :=
    CFSG.LocalCores.comap_center_eq_of_perfect hC φ hφ (hYq.trans hkerq)
  have hmap : Subgroup.map φ q.ker = Subgroup.center D := by
    rw [hkerq', ← hcomapφ]
    exact Subgroup.map_comap_eq_self_of_surjective hφ _
  let e : C ⧸ φ.ker ≃* D := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let qbar : D →* M := (QuotientGroup.lift φ.ker q hYq).comp e.symm.toMonoidHom
  have hqbar_apply : ∀ c : C, qbar (φ c) = q c := by
    intro c
    have h1 : e.symm (φ c) = (↑c : C ⧸ φ.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact QuotientGroup.kerLift_mk φ c
    show (QuotientGroup.lift φ.ker q hYq) (e.symm (φ c)) = q c
    rw [h1]
    exact QuotientGroup.lift_mk' φ.ker hYq c
  have hsurj : Function.Surjective qbar := by
    intro m
    obtain ⟨c, rfl⟩ := hq m
    exact ⟨φ c, hqbar_apply c⟩
  have hkereq : qbar.ker = Subgroup.center D := by
    rw [← hmap]
    ext d
    constructor
    · intro hd
      obtain ⟨c, rfl⟩ := hφ d
      rw [MonoidHom.mem_ker, hqbar_apply] at hd
      exact Subgroup.mem_map_of_mem φ (MonoidHom.mem_ker.mpr hd)
    · rintro ⟨c, hc, rfl⟩
      exact MonoidHom.mem_ker.mpr (by rw [hqbar_apply]; exact MonoidHom.mem_ker.mp hc)
  have hcenter : Nat.card (Subgroup.center D) = 2 := by
    let θ : ↥q.ker →* ↥(Subgroup.center D) :=
      { toFun := fun x => ⟨φ x, by
          have hx : φ (x : C) ∈ Subgroup.map φ q.ker := Subgroup.mem_map_of_mem φ x.2
          rwa [hmap] at hx⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hθ : Function.Surjective θ := by
      intro z
      have hz : (z : D) ∈ Subgroup.map φ q.ker := by rw [hmap]; exact z.2
      obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hz
      exact ⟨⟨c, hc⟩, Subtype.ext hce⟩
    have hkerθ : θ.ker = φ.ker.subgroupOf q.ker := by
      ext x
      simp [θ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv, hkerθ] at h1
    have h2 : Nat.card ↥(φ.ker.subgroupOf q.ker) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYq).toEquiv, hcardY]
    rw [h2, hcard] at h1
    omega
  exact ⟨qbar, hsurj, hkereq, hcenter⟩

theorem map_mk'_self_centralizing {G : Type*} [Group G] {N C Y : Subgroup G} (hCN : C ≤ N)
    [hYn : (Y.subgroupOf N).Normal] (hYc : ∀ y ∈ Y, ∀ c ∈ C, y * c = c * y)
    (hperf : Group.IsPerfect ↥C) (hcent : ∀ g ∈ N, (∀ c ∈ C, g * c = c * g) → g ∈ C)
    (g : ↥N) (hgnorm : ∀ c ∈ C, (g : G) * c * (g : G)⁻¹ ∈ C)
    (hg : ∀ d ∈ (C.subgroupOf N).map (QuotientGroup.mk' (Y.subgroupOf N)),
      QuotientGroup.mk' (Y.subgroupOf N) g * d = d * QuotientGroup.mk' (Y.subgroupOf N) g) :
    QuotientGroup.mk' (Y.subgroupOf N) g ∈
      (C.subgroupOf N).map (QuotientGroup.mk' (Y.subgroupOf N)) := by
  let mk : ↥N →* (↥N ⧸ Y.subgroupOf N) := QuotientGroup.mk' (Y.subgroupOf N)
  have hcommY : ∀ c ∈ C, (g : G) * c * (g : G)⁻¹ * c⁻¹ ∈ Y := by
    intro c hc
    have hmem : mk (⟨c, hCN hc⟩ : ↥N) ∈ (C.subgroupOf N).map mk :=
      Subgroup.mem_map_of_mem mk (show (⟨c, hCN hc⟩ : ↥N) ∈ C.subgroupOf N from hc)
    have h1 : mk g * mk ⟨c, hCN hc⟩ = mk ⟨c, hCN hc⟩ * mk g := hg _ hmem
    have h2 : mk (g * ⟨c, hCN hc⟩ * g⁻¹ * ⟨c, hCN hc⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 : (g * ⟨c, hCN hc⟩ * g⁻¹ * ⟨c, hCN hc⟩⁻¹ : ↥N) ∈ Y.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      exact h2
    simpa [Subgroup.mem_subgroupOf] using h3
  have hnc : (g : G) ∈ C :=
    hcent (g : G) g.2 (mul_comm_of_isPerfect_of_commutator_mem hperf hYc hgnorm hcommY)
  exact Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hnc)

end CFSG.GroupTheory

namespace CFSG.Quasithin.TwoM22

open Subgroup CFSG.Blueprint

theorem mul_self_eq_one_of_isTwoM22TwoModel_of_card_ker_eq_six
    {W : Type} [Group W] [Finite W] {M : Subgroup W} {T : W} (hmod : IsTwoM22TwoModel M T)
    {G : Type} [Group G] [Finite G] {N C Y : Subgroup G} (hCN : C ≤ N)
    (hnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hidx : C.relIndex N = 2)
    (hcent : ∀ g ∈ N, (∀ c ∈ C, g * c = c * g) → g ∈ C)
    (hperf : Group.IsPerfect ↥C)
    (q : ↥C →* ↥CFSG.Blueprint.NativeSporadic.M22) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center ↥C) (hcard : Nat.card q.ker = 6)
    (hYC : Y ≤ C) (hY : Nat.card Y = 3) (hYker : ∀ y (hy : y ∈ Y), q ⟨y, hYC hy⟩ = 1)
    (hYN : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y)
    {t : G} (htN : t ∈ N) (htC : t ∉ C) (htt : t * t = 1)
    (htY : ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹)
    {n : G} (hnN : n ∈ N) (hnC : n ∉ C) (hn : ∀ c ∈ C, n * n * c = c * (n * n)) :
    n * n = 1 := by
  haveI hYNnorm : (Y.subgroupOf N).Normal :=
    ⟨fun y hy g => by
      have h := hYN (g : G) g.2 (y : G) (Subgroup.mem_subgroupOf.mp hy)
      simpa [Subgroup.mem_subgroupOf] using h⟩
  haveI hCNnorm : (C.subgroupOf N).Normal :=
    ⟨fun c hc g => by
      have h := hnorm (g : G) g.2 (c : G) (Subgroup.mem_subgroupOf.mp hc)
      simpa [Subgroup.mem_subgroupOf] using h⟩
  let Q := ↥N ⧸ Y.subgroupOf N
  let mk : ↥N →* Q := QuotientGroup.mk' (Y.subgroupOf N)
  let CN : Subgroup ↥N := C.subgroupOf N
  let D : Subgroup Q := CN.map mk
  have hmkker : mk.ker = Y.subgroupOf N := QuotientGroup.ker_mk' _
  have hmksurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hidxCN : CN.index = 2 := by
    have h1 : CN.relIndex (⊤ : Subgroup ↥N) = C.relIndex N := by
      simpa only [Subgroup.subgroupOf_self] using
        Subgroup.relIndex_subgroupOf (H := C) (K := N) (L := N) le_rfl
    rwa [Subgroup.relIndex_top_right, hidx] at h1
  have hDnorm : D.Normal := hCNnorm.map mk hmksurj
  haveI : D.Normal := hDnorm
  have hidxD : D.index = 2 := by
    have hkerle : mk.ker ≤ CN := by
      intro y hy
      rw [hmkker] at hy
      exact hYC (Subgroup.mem_subgroupOf.mp hy)
    rw [show D = CN.map mk from rfl, Subgroup.index_map_eq CN hmksurj hkerle, hidxCN]
  have hperfCN : Group.IsPerfect ↥CN := by
    haveI : Group.IsPerfect ↥C := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hCN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hCN).symm.surjective
  haveI : Group.IsPerfect ↥CN := hperfCN
  have hperfD : Group.IsPerfect ↥D := Group.IsPerfect.map (H := CN) mk
  let φ : ↥C →* ↥D :=
    { toFun := fun c =>
        ⟨mk ⟨(c : G), hCN c.2⟩,
          Subgroup.mem_map_of_mem mk (show (⟨(c : G), hCN c.2⟩ : ↥N) ∈ CN from c.2)⟩
      map_one' := by
        apply Subtype.ext
        show mk (1 : ↥N) = 1
        exact map_one mk
      map_mul' := fun a b => by
        apply Subtype.ext
        show mk ((⟨(a : G), hCN a.2⟩ : ↥N) * ⟨(b : G), hCN b.2⟩)
          = mk ⟨(a : G), hCN a.2⟩ * mk ⟨(b : G), hCN b.2⟩
        exact map_mul mk _ _ }
  have hφ : Function.Surjective φ := by
    intro d
    obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp d.2
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    apply Subtype.ext
    show mk x = (d : Q)
    exact hxd
  have hφker : φ.ker = Y.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h2 : mk (⟨(c : G), hCN c.2⟩ : ↥N) = 1 := congrArg Subtype.val h
      have h3 : (⟨(c : G), hCN c.2⟩ : ↥N) ∈ Y.subgroupOf N := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
        exact h2
      simpa [Subgroup.mem_subgroupOf] using h3
    · intro h
      apply Subtype.ext
      show mk (⟨(c : G), hCN c.2⟩ : ↥N) = 1
      have h2 : (⟨(c : G), hCN c.2⟩ : ↥N) ∈ Y.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_subgroupOf.mp h
      show (QuotientGroup.mk' (Y.subgroupOf N)) (⟨(c : G), hCN c.2⟩ : ↥N) = 1
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr h2
  have hφker_card : Nat.card φ.ker = 3 := by
    rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv]
    exact hY
  have hφq : φ.ker ≤ q.ker := by
    intro c hc
    rw [hφker] at hc
    have hcY : (c : G) ∈ Y := Subgroup.mem_subgroupOf.mp hc
    rw [MonoidHom.mem_ker]
    simpa using hYker (c : G) hcY
  have hYcentral : ∀ y ∈ Y, ∀ c ∈ C, y * c = c * y := by
    intro y hy c hc
    have hyZ : (⟨y, hYC hy⟩ : ↥C) ∈ Subgroup.center ↥C :=
      hker (by rw [MonoidHom.mem_ker]; exact hYker y hy)
    have hcy : (⟨c, hc⟩ : ↥C) * ⟨y, hYC hy⟩ = ⟨y, hYC hy⟩ * ⟨c, hc⟩ :=
      Subgroup.mem_center_iff.mp hyZ ⟨c, hc⟩
    simpa using hcy.symm
  have hDcent : ∀ g : Q, (∀ d ∈ D, g * d = d * g) → g ∈ D := by
    intro g hg
    obtain ⟨n0, rfl⟩ := hmksurj g
    exact CFSG.GroupTheory.map_mk'_self_centralizing hCN hYcentral hperf hcent n0
      (fun c hc => hnorm (n0 : G) n0.2 c hc) hg
  obtain ⟨qbar, hqbar_surj, hqbar_ker, hqbar_card⟩ :=
    CFSG.GroupTheory.exists_lift_ker_eq_center_of_isPerfect_of_ker_le hperf q hq hker
      CFSG.Sporadic.Schreier.m22_center_eq_bot' φ hφ hφq hcard hφker_card
  let tN : ↥N := ⟨t, htN⟩
  let nN : ↥N := ⟨n, hnN⟩
  have htCN : tN ∉ CN := fun h => htC (Subgroup.mem_subgroupOf.mp h)
  have hnCN : nN ∉ CN := fun h => hnC (Subgroup.mem_subgroupOf.mp h)
  have hsD : mk tN ∉ D := by
    intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hmem
    have hce' : mk c = mk tN := hce
    have h1 : (c⁻¹ * tN : ↥N) ∈ Y.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      show mk (c⁻¹ * tN) = 1
      rw [map_mul, map_inv, hce', inv_mul_cancel]
    have h2 : ((c⁻¹ * tN : ↥N) : G) ∈ Y := Subgroup.mem_subgroupOf.mp h1
    have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    exact htC (by
      have h4 : (c : G) * ((c⁻¹ * tN : ↥N) : G) ∈ C := C.mul_mem hcC (hYC h2)
      have h5 : (c : G) * ((c⁻¹ * tN : ↥N) : G) = t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, tN]
        group
      rwa [h5] at h4)
  have hnD : mk nN ∉ D := by
    intro hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hmem
    have hce' : mk c = mk nN := hce
    have h1 : (c⁻¹ * nN : ↥N) ∈ Y.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      show mk (c⁻¹ * nN) = 1
      rw [map_mul, map_inv, hce', inv_mul_cancel]
    have h2 : ((c⁻¹ * nN : ↥N) : G) ∈ Y := Subgroup.mem_subgroupOf.mp h1
    have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    exact hnC (by
      have h4 : (c : G) * ((c⁻¹ * nN : ↥N) : G) ∈ C := C.mul_mem hcC (hYC h2)
      have h5 : (c : G) * ((c⁻¹ * nN : ↥N) : G) = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, nN]
        group
      rwa [h5] at h4)
  have hs : mk tN * mk tN = 1 := by
    have h1 : tN * tN = 1 := by
      apply Subtype.ext
      simpa [tN] using htt
    rw [← map_mul, h1, map_one]
  have hnc : ∀ d ∈ D, mk nN * mk nN * d = d * (mk nN * mk nN) := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hd
    have h1 : nN * nN * c = c * (nN * nN) := by
      apply Subtype.ext
      simpa [nN] using hn (c : G) (Subgroup.mem_subgroupOf.mp hc)
    show mk nN * mk nN * mk c = mk c * (mk nN * mk nN)
    simp only [← map_mul]
    rw [h1]
  have hsq : mk nN * mk nN = 1 :=
    mul_self_eq_one_of_isTwoM22TwoModel hmod D hidxD hperfD qbar hqbar_surj hqbar_ker
      hqbar_card hDcent hsD hs hnD hnc
  have hnnY : n * n ∈ Y := by
    have h1 : mk (nN * nN) = 1 := by rw [map_mul, hsq]
    have h2 : (nN * nN) ∈ Y.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      exact h1
    simpa [Subgroup.mem_subgroupOf, nN] using h2
  have hntC : n * t ∈ C := by
    have hmem : nN * tN ∈ CN :=
      (Subgroup.mul_mem_iff_of_index_two hidxCN).mpr
        ⟨fun h => absurd h hnCN, fun h => absurd h htCN⟩
    have hmem' : ((nN * tN : ↥N) : G) ∈ C := Subgroup.mem_subgroupOf.mp hmem
    simpa [nN, tN] using hmem'
  have hntinv : ∀ y ∈ Y, n * y * n⁻¹ = y⁻¹ := by
    intro y hy
    have hnt_comm : y⁻¹ * (n * t) = (n * t) * y⁻¹ :=
      hYcentral y⁻¹ (Y.inv_mem hy) (n * t) hntC
    have hnt_conj : (n * t) * y⁻¹ * (n * t)⁻¹ = y⁻¹ := by
      rw [← hnt_comm]; group
    have htin : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hty : t * y * t = y⁻¹ := by simpa [htin] using htY y hy
    have hn_eq : n = (n * t) * t := by rw [mul_assoc, htt, mul_one]
    calc n * y * n⁻¹ = ((n * t) * t) * y * (t * (n * t)⁻¹) := by
          conv_lhs => rw [hn_eq, mul_inv_rev, htin]
      _ = (n * t) * (t * y * t) * (n * t)⁻¹ := by group
      _ = (n * t) * y⁻¹ * (n * t)⁻¹ := by rw [hty]
      _ = y⁻¹ := hnt_conj
  have hy2 : (n * n) * (n * n) = 1 := by
    have h1 : n * (n * n) * n⁻¹ = (n * n)⁻¹ := hntinv (n * n) hnnY
    have h2 : n * (n * n) * n⁻¹ = n * n := by group
    rw [h2] at h1
    calc (n * n) * (n * n) = (n * n)⁻¹ * (n * n) := by rw [← h1]
      _ = 1 := inv_mul_cancel _
  have hy3 : (n * n) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨n * n, hnnY⟩ : ↥Y))
    rw [hY] at h
    simpa using congrArg Subtype.val h
  have h3 : n * n = (n * n) ^ 3 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, hy2, one_mul]
  rw [← h3] at hy3
  exact hy3
