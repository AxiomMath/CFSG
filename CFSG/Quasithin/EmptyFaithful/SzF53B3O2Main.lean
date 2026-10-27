module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O2Geo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53Mod.O2 CFSG.Quasithin.CosetGeom

namespace F53B3

namespace O2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_image_eq_That (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S)
    {x y z μ : Geo H M} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hμ : vtype μ = true)
    (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) (hz : z ∈ nbrs μ)
    (Dx : OrthDatum (stab x) (Zv x) (Vn x) (stab μ ⊓ stab x) (Vn x ⊓ Vn y))
    (Dy : OrthDatum (stab y) (Zv y) (Vn y) (stab μ ⊓ stab y) (Vn x ⊓ Vn y))
    (Dz : OrthDatum (stab z) (Zv z) (Vn z) (stab μ ⊓ stab z) (Vn x ⊓ Vn y))
    (hN4 : ((Vn x).subgroupOf (stab y)).map Dy.Ψ = S5That) : False := by
  have hA := hB.amalgam
  have hBase := hB.toB3Base
  have hRn : stab μ ≤ Subgroup.normalizer ((Vn x ⊓ Vn y : Subgroup G) : Set G) :=
    hBl.vn_inf_normal y μ x hxy.symm hμ hx hy
  have hR8 : Nat.card ↥(Vn x ⊓ Vn y) = 8 := hC1.card_R x y μ hxy hμ hx hy
  have hZR : Zv μ ≤ Vn x ⊓ Vn y := le_inf (Zv_mu_le_Vn hx) (Zv_mu_le_Vn hy)
  have hQx : Qv μ ≤ stab x := Qv_le_stab_of_mem_nbrs hA hx
  have hQy : Qv μ ≤ stab y := Qv_le_stab_of_mem_nbrs hA hy
  have hQz : Qv μ ≤ stab z := Qv_le_stab_of_mem_nbrs hA hz
  have hVxQ : Vn x ≤ Qv μ := Vn_le_Qv_mu hBl hx
  have hRle : Vn x ⊓ Vn y ≤ Vn x ⊓ Qv y :=
    le_inf inf_le_left (inf_le_right.trans (N37.Vn_le_Qv_self hBl y))
  have hR4 : (Vn x ⊓ Vn y).relIndex (Vn x) = 4 := by
    have h := Subgroup.relIndex_mul_card (Vn x ⊓ Vn y) (Vn x)
    rw [inf_of_le_left inf_le_left, hR8, card_Vn hB hBl hC1 hμ hx] at h
    omega
  have hker : Dy.Ψ.ker = (Qv y).subgroupOf (stab y) := Dy.ker_eq
  have hidx : (Vn x ⊓ Qv y).relIndex (Vn x) =
      Nat.card ↥(((Vn x).subgroupOf (stab y)).map Dy.Ψ) := by
    have h1 := Subgroup.relIndex_ker (K := (Vn x).subgroupOf (stab y)) Dy.Ψ
    rw [hker, Subgroup.relIndex_subgroupOf (hVxQ.trans hQy)] at h1
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact h1
  have hJ4 : (Vn x ⊓ Qv y).relIndex (Vn x) = 4 := by rw [hidx, hN4, card_S5That]
  have hVxQy : Vn x ⊓ Qv y = Vn x ⊓ Vn y := by
    have h := Subgroup.relIndex_mul_relIndex (Vn x ⊓ Vn y) (Vn x ⊓ Qv y) (Vn x) hRle inf_le_left
    rw [hJ4, hR4] at h
    have h1 : (Vn x ⊓ Vn y).relIndex (Vn x ⊓ Qv y) = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hRle
  have hΛ : ∀ (q : G) (hq : q ∈ Qv μ),
      Dx.Ψ ⟨q, hQx hq⟩ ∈ S5That ↔ Dy.Ψ ⟨q, hQy hq⟩ ∈ S5That := by
    intro q hq
    have hqSx : q ∈ stab μ ⊓ stab x := ⟨N37.Qv_le_stab_self μ hq, hQx hq⟩
    rw [← Dx.kerX ⟨q, hQx hq⟩ hqSx]
    constructor
    · intro h
      refine S5That_centralizer _ (Ψ_mem_S5Syl hBase hμ hy Dy hq) fun t ht => ?_
      rw [← hN4] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      have hv' : (v : G) ∈ Vn x := Subgroup.mem_subgroupOf.mp hv
      have hc := h (v : G) hv'
      rw [← hVxQy] at hc
      exact (Dy.comm_iff ⟨q, hQy hq⟩ v).mpr hc.2
    · intro h v hv
      have hvy : v ∈ stab y := (hVxQ.trans hQy) hv
      have hmem : Dy.Ψ ⟨v, hvy⟩ ∈ S5That := by
        rw [← hN4]
        exact ⟨⟨v, hvy⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
      have hcomm := (Dy.comm_iff ⟨q, hQy hq⟩ ⟨v, hvy⟩).mp (S5That_comm _ h _ hmem)
      have hnorm : q * v * q⁻¹ ∈ Vn x :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn x (hQx hq)) v).mp hv
      rw [← hVxQy]
      exact ⟨(Vn x).mul_mem hnorm ((Vn x).inv_mem hv), hcomm⟩
  obtain ⟨r₀, hr₀, hr₀Z⟩ := exists_not_mem_Zv hBl hμ hR8
  have hθ : ∀ w ∈ nbrs μ, ∀ D : OrthDatum (stab w) (Zv w) (Vn w) (stab μ ⊓ stab w) (Vn x ⊓ Vn y),
      ∀ q : ↥(stab w), (q : G) ∈ Qv μ → (D.Ψ q ∈ S5That ↔ (q : G) * r₀ * (q : G)⁻¹ * r₀⁻¹ ∈ Zv w) :=
    fun w _ D q hq => datum_iff_comm hBase hBl hμ hZR hR8 hRn D hr₀ hr₀Z hq
  obtain ⟨τ, hτS, hτT⟩ := exists_S5Syl_not_S5That
  obtain ⟨qz, hqz, hqzτ⟩ := exists_Qmu_image hBase hμ hz Dz hτS
  have hqzz : ¬ (qz : G) * r₀ * (qz : G)⁻¹ * r₀⁻¹ ∈ Zv z := by
    rw [← hθ z hz Dz qz hqz, hqzτ]
    exact hτT
  set q : G := (qz : G) with hqdef
  have ht : q * r₀ * q⁻¹ * r₀⁻¹ ∈ Zv μ := comm_mem_Zv hBase hBl hμ hZR hR8 hRn hqz hr₀
  rcases Zv_subset_union hBase hBl hμ hx hy hz hxy hxz hyz _ ht with h | h | h
  · have h1 := (hθ x hx Dx ⟨q, hQx hqz⟩ hqz).mpr h
    have h2 := (hθ y hy Dy ⟨q, hQy hqz⟩ hqz).mp ((hΛ q hqz).mp h1)
    exact hqzz (by rw [Zv_inf_Zv hBase hμ hxy hx hy h h2]; exact (Zv z).one_mem)
  · have h1 := (hθ y hy Dy ⟨q, hQy hqz⟩ hqz).mpr h
    have h2 := (hθ x hx Dx ⟨q, hQx hqz⟩ hqz).mp ((hΛ q hqz).mpr h1)
    exact hqzz (by rw [Zv_inf_Zv hBase hμ hxy hx hy h2 h]; exact (Zv z).one_mem)
  · exact hqzz h

theorem key (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S) {x y μ : Geo H M}
    (hxy : x ≠ y) (hμ : vtype μ = true) (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) :
    (Vn x ⊓ Qv y).relIndex (Vn x) = 2 ∧ Vn x ≤ oTwoRes (stab y) ⊔ Qv y := by
  have hA := hB.amalgam
  have hBase := hB.toB3Base
  obtain ⟨z, hz, hzx, hzy⟩ := exists_third_nbr hA hμ hxy
  have hRn : stab μ ≤ Subgroup.normalizer ((Vn x ⊓ Vn y : Subgroup G) : Set G) :=
    hBl.vn_inf_normal y μ x hxy.symm hμ hx hy
  have hR8 : Nat.card ↥(Vn x ⊓ Vn y) = 8 := hC1.card_R x y μ hxy hμ hx hy
  have hRz : Vn x ⊓ Vn y ≤ Vn z :=
    inf_le_Vn_third hBase hBl hμ hx hy hz hxy hzx.symm hzy.symm
  obtain ⟨Dx⟩ := local_datum hB hC1 hμ hx (Zv_le_inf hBl hμ hx hy hx) inf_le_left hRn hR8
  obtain ⟨Dy⟩ := local_datum hB hC1 hμ hy (Zv_le_inf hBl hμ hx hy hy) inf_le_right hRn hR8
  obtain ⟨Dz⟩ := local_datum hB hC1 hμ hz (Zv_le_inf hBl hμ hx hy hz) hRz hRn hR8
  have hQy : Qv μ ≤ stab y := Qv_le_stab_of_mem_nbrs hA hy
  have hQx : Qv μ ≤ stab x := Qv_le_stab_of_mem_nbrs hA hx
  have hVxQ : Vn x ≤ Qv μ := Vn_le_Qv_mu hBl hx
  have hVxy : Vn x ≤ stab y := hVxQ.trans hQy
  have hxf := vtype_nbr_of_true hx hμ
  set N : Subgroup (Equiv.Perm (Fin 5)) := ((Vn x).subgroupOf (stab y)).map Dy.Ψ with hNdef
  have hNT : N ≤ S5That := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : (v : G) ∈ Vn x := Subgroup.mem_subgroupOf.mp hv
    refine (Dy.kerU v ⟨N37.Qv_le_stab_self μ (hVxQ hv'), v.2⟩).mp fun u hu => ?_
    have hc : (v : G) * u = u * (v : G) :=
      N37.elemAbelian_comm (hBl.elemAbelian_vn x) hv' hu.1
    rw [comm_eq_one_iff.mpr hc]
    exact (Zv y).one_mem
  have hNn : ∀ s ∈ S5Syl, ∀ b ∈ N, s * b * s⁻¹ ∈ N := by
    intro s hs b hb
    obtain ⟨q, hq, rfl⟩ := exists_Qmu_image hBase hμ hy Dy hs
    obtain ⟨v, hv, rfl⟩ := hb
    have hv' : (v : G) ∈ Vn x := Subgroup.mem_subgroupOf.mp hv
    have hmem : (q * v * q⁻¹ : ↥(stab y)) ∈ (Vn x).subgroupOf (stab y) := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn x (hQx hq)) v).mp hv'
    exact ⟨_, hmem, by simp [map_mul, map_inv]⟩
  have hdist : dist x y = 2 := N37.dist_eq_two_of_nbrs hx hy hxy
  have hN0 : N ≠ ⊥ := by
    obtain ⟨v, hvV, hvQ⟩ := IsConcreteLE.not_le_iff_exists.mp (hBl.not_vn_le_qv x y hxf hdist)
    intro hbot
    have hmem : Dy.Ψ ⟨v, hVxy hvV⟩ ∈ N := ⟨_, Subgroup.mem_subgroupOf.mpr hvV, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hvQ ((Dy.ker _).mp hmem)
  have hidx : (Vn x ⊓ Qv y).relIndex (Vn x) = Nat.card ↥N := by
    have h1 := Subgroup.relIndex_ker (K := (Vn x).subgroupOf (stab y)) Dy.Ψ
    rw [Dy.ker_eq, Subgroup.relIndex_subgroupOf hVxy] at h1
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact h1
  rcases S5That_dichotomy N hNT hNn hN0 with ⟨hN2, hNA⟩ | hN4
  · refine ⟨by rw [hidx, hN2], fun v hv => ?_⟩
    exact (Dy.odd ⟨v, hVxy hv⟩).mpr (hNA ⟨⟨v, hVxy hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩)
  · exact (not_image_eq_That hB hBl hC1 hxy hzx.symm hzy.symm hμ hx hy hz Dx Dy Dz hN4).elim

end O2

theorem orthS4 {G : Type} [Group G] [Finite G] {H M S : Subgroup G} (hB : B3FactsO H M S)
    (hBl : B3Block H M S) (hC1 : OrthC1 H M S) : OrthS4 H M S where
  index_two := fun _ _ _ hxy hμ hx hy => (O2.key hB hBl hC1 hxy hμ hx hy).1
  le_A5 := fun _ _ _ hxy hμ hx hy => (O2.key hB hBl hC1 hxy hμ hx hy).2

end F53B3

end CFSG.Quasithin
