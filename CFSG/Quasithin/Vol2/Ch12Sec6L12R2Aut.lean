module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12R1Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6L12R2CharTwo
public import CFSG.Quasithin.Vol2.Ch12Sec6L12b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section AutBar

variable {G : Type*} [Group G] (K : Subgroup G)

theorem map_center_eq (φ : MulAut ↥K) :
    (Subgroup.center ↥K).map φ.toMonoidHom = Subgroup.center ↥K :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance φ

noncomputable def autBarHom : ↥(Subgroup.normalizer (K : Set G)) →*
    MulAut (↥K ⧸ Subgroup.center ↥K) where
  toFun x := QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K)
    (K.normalizerMonoidHom x) (map_center_eq K _)
  map_one' := by
    ext k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    simp [QuotientGroup.congr_mk]
  map_mul' x y := by
    ext k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    rw [MulAut.mul_apply]
    erw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    rw [map_mul]
    rfl

theorem autBarHom_mk (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    autBarHom K x (QuotientGroup.mk k) = QuotientGroup.mk (K.normalizerMonoidHom x k) :=
  QuotientGroup.congr_mk _ _ (K.normalizerMonoidHom x) (map_center_eq K _) k

theorem coe_normalizerMonoidHom (x : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    ((K.normalizerMonoidHom x k : ↥K) : G) = (x : G) * k * (x : G)⁻¹ := rfl

theorem autBarHom_apply_of_comm (x : ↥(Subgroup.normalizer (K : Set G))) {k : G} (hk : k ∈ K)
    (hc : (x : G) * k = k * (x : G)) :
    autBarHom K x (QuotientGroup.mk ⟨k, hk⟩) = QuotientGroup.mk ⟨k, hk⟩ := by
  rw [autBarHom_mk]
  congr 1
  apply Subtype.ext
  rw [coe_normalizerMonoidHom, hc, mul_inv_cancel_right]

theorem autBarHom_of_mem (x : ↥(Subgroup.normalizer (K : Set G))) (hxK : (x : G) ∈ K) :
    autBarHom K x = MulAut.conj (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
  ext k
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  rw [autBarHom_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem mem_centralizer_of_autBarHom_eq_one (hK : ⁅K, K⁆ = K)
    (x : ↥(Subgroup.normalizer (K : Set G))) (h : autBarHom K x = 1) :
    (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hy : ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
    intro k hk
    have h1 := congrArg (fun f : MulAut (↥K ⧸ Subgroup.center ↥K) => f (QuotientGroup.mk ⟨k, hk⟩)) h
    simp only [autBarHom_mk, MulAut.one_apply, QuotientGroup.eq] at h1
    set z : ↥K := (K.normalizerMonoidHom x ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ with hz
    have hzc := Subgroup.mem_center_iff.1 h1
    have hzC : ∀ w ∈ K, w * (z : G) = (z : G) * w := fun w hw =>
      congrArg Subtype.val (hzc ⟨w, hw⟩)
    have hzG : (z : G) = ((x : G) * k * (x : G)⁻¹)⁻¹ * k := by
      rw [hz]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_normalizerMonoidHom]
    have hkz : k * (z : G)⁻¹ = (z : G)⁻¹ * k := by
      have := hzC k hk
      calc k * (z : G)⁻¹ = (z : G)⁻¹ * (z * k) * (z : G)⁻¹ := by group
        _ = (z : G)⁻¹ * (k * z) * (z : G)⁻¹ := by rw [this]
        _ = (z : G)⁻¹ * k := by group
    have e1 : (x : G) * k * (x : G)⁻¹ * k⁻¹ = (z : G)⁻¹ := by
      have hx' : (x : G) * k * (x : G)⁻¹ = k * (z : G)⁻¹ := by
        rw [hzG]; group
      rw [hx', hkz]; group
    rw [e1]
    refine ⟨K.inv_mem z.2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have := hzC w hw
    calc w * (z : G)⁻¹ = (z : G)⁻¹ * (z * w * (z : G)⁻¹) := by group
      _ = (z : G)⁻¹ * (w * z * (z : G)⁻¹) := by rw [this]
      _ = (z : G)⁻¹ * w := by group
  exact S126T2.mem_centralizer_of_comm_mem_center hK hy

end AutBar

section EndGame

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem false_of_charTwo_centralizer (x : ↥(Subgroup.normalizer (K : Set G)))
    (hD : IsSimpleGroup ↥(perfectCore (autCentralizer (autBarHom K x))))
    (hD2 : ¬ IsPGroup 2 ↥(perfectCore (autCentralizer (autBarHom K x))))
    (hC : CharTwo (K ⊓ Subgroup.centralizer ({(x : G)} : Set G))) : False := by
  classical
  set Z := Subgroup.center ↥K with hZ
  set ρ : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z with hρ
  set α := autBarHom K x with hα
  set Pb := autCentralizer α with hPb
  set Db := perfectCore Pb with hDb
  set P : Subgroup ↥K := Pb.comap ρ with hP
  set Cu : Subgroup ↥K := (Subgroup.centralizer ({(x : G)} : Set G)).comap K.subtype with hCu
  have hmemP : ∀ a : ↥K, a ∈ P ↔ (K.normalizerMonoidHom x a)⁻¹ * a ∈ Z := by
    intro a
    rw [hP, Subgroup.mem_comap, hPb, mem_autCentralizer, hα, hρ, QuotientGroup.mk'_apply,
      autBarHom_mk, QuotientGroup.eq]
  have h1 : ⁅P, P⁆ ≤ Cu := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    set φ := K.normalizerMonoidHom x with hφ
    have ha' : (φ a)⁻¹ * a ∈ Z := (hmemP a).1 ha
    have hb' : (φ b)⁻¹ * b ∈ Z := (hmemP b).1 hb
    have key : ∀ c : ↥K, (φ c)⁻¹ * c ∈ Z → ∃ z ∈ Z, φ c = z * c := by
      intro c hc
      refine ⟨((φ c)⁻¹ * c)⁻¹, Subgroup.inv_mem _ hc, ?_⟩
      have hc' := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hc) c
      calc φ c = c * ((φ c)⁻¹ * c)⁻¹ := by group
        _ = ((φ c)⁻¹ * c)⁻¹ * c := hc'
    obtain ⟨za, hza, hφa⟩ := key a ha'
    obtain ⟨zb, hzb, hφb⟩ := key b hb'
    have hcomm : φ ⁅a, b⁆ = ⁅a, b⁆ := by
      have e : φ ⁅a, b⁆ = (za * a) * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹ := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hφa, hφb]
      rw [e, S126T2.comm_mul_central (Subgroup.mem_center_iff.1 hza a).symm
        (Subgroup.mem_center_iff.1 hza b).symm (Subgroup.mem_center_iff.1 hzb a).symm
        (Subgroup.mem_center_iff.1 hzb b).symm (Subgroup.mem_center_iff.1 hzb za),
        commutatorElement_def]
    show ((⁅a, b⁆ : ↥K) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 := congrArg Subtype.val hcomm
    rw [hφ, coe_normalizerMonoidHom] at h3
    calc (⁅a, b⁆ : ↥K).1 * (x : G) = (x : G) * (⁅a, b⁆ : ↥K).1 * (x : G)⁻¹ * (x : G) := by rw [h3]
      _ = (x : G) * (⁅a, b⁆ : ↥K).1 := by group
  have hPmap : P.map ρ = Pb :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Pb
  have hDbPb : Db ≤ ⁅Pb, Pb⁆ := perfectCore_le_derivedSeriesOf Pb 1
  have h2 : Db ≤ Cu.map ρ := by
    refine hDbPb.trans ?_
    rw [← hPmap, ← Subgroup.map_commutator]
    exact Subgroup.map_mono h1
  set N : Subgroup ↥K := Cu ⊓ Db.comap ρ with hN
  have hNmap : N.map ρ = Db := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      exact hn.2
    · intro d hd
      obtain ⟨c, hc, rfl⟩ := h2 hd
      exact ⟨c, ⟨hc, hd⟩, rfl⟩
  set N' : Subgroup G := N.map K.subtype with hN'
  have hN'K : N' ≤ K := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hN'C : N' ≤ K ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n.2, hn.1⟩
  have hCuP : ∀ g : ↥K, g ∈ Cu → g ∈ P := by
    intro g hg
    rw [hmemP]
    have h3 : (x : G) * (g : G) = (g : G) * (x : G) :=
      (Subgroup.mem_centralizer_singleton_iff.1 hg).symm
    have h4 : K.normalizerMonoidHom x g = g := by
      apply Subtype.ext
      rw [coe_normalizerMonoidHom, h3, mul_inv_cancel_right]
    rw [h4, inv_mul_cancel]
    exact Z.one_mem
  have hnorm : (N'.subgroupOf (K ⊓ Subgroup.centralizer ({(x : G)} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN'C]
    rintro _ g ⟨n, hn, rfl⟩ hg
    set g' : ↥K := ⟨g, hg.1⟩ with hg'
    have hg'Cu : g' ∈ Cu := hg.2
    refine ⟨g' * n * g'⁻¹, ⟨Cu.mul_mem (Cu.mul_mem hg'Cu hn.1) (Cu.inv_mem hg'Cu), ?_⟩, rfl⟩
    have hDn : Db.comap ρ ⊓ Db.comap ρ = Db.comap ρ := inf_idem _
    have h5 := (Subgroup.normal_subgroupOf_iff (perfectCore_le Pb)).1 (perfectCore_normal Pb)
      (ρ n) (ρ g') hn.2 (by rw [← hPmap]; exact ⟨g', hCuP g' hg'Cu, rfl⟩)
    simpa [map_mul, map_inv] using h5
  have hCN' : CharTwo N' := CharTwo.of_normal hC hN'C hnorm
  let ψ₀ : ↥N' →* ↥K ⧸ Z := ρ.comp (Subgroup.inclusion hN'K)
  have hψ₀ : ∀ y : ↥N', ψ₀ y ∈ Db := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact hn.2
  let ψ : ↥N' →* ↥Db := ψ₀.codRestrict Db hψ₀
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, hd⟩
    obtain ⟨n, hn, hnd⟩ := (hNmap.symm ▸ hd : d ∈ N.map ρ)
    exact ⟨⟨K.subtype n, ⟨n, hn, rfl⟩⟩, Subtype.ext hnd⟩
  have hker : ∀ y : ↥N', ψ y = 1 → y ∈ Subgroup.center ↥N' := by
    intro y hy
    have h6 : ψ₀ y = 1 := congrArg Subtype.val hy
    have h7 : Subgroup.inclusion hN'K y ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
      exact h6
    rw [Subgroup.mem_center_iff]
    intro g
    have h8 := Subgroup.mem_center_iff.1 h7 (Subgroup.inclusion hN'K g)
    have h9 := congrArg Subtype.val h8
    exact Subtype.ext h9
  exact false_of_charTwo_cover hCN' ψ hψs hker hD hD2

end EndGame

end CFSG.Quasithin.H13
