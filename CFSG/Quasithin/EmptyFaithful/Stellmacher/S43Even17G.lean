module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17E
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43'

variable {α : Geo H M}

theorem relIndex_inf_le_two (hA : F53Amalgam H M S) {α₂ α₃ α' : Geo H M}
    (h2v : vtype α₂ = false) (h3 : α₃ ∈ nbrs α₂) (h' : α' ∈ nbrs α₃) {K : Subgroup G}
    (hK : K ≤ stab α₂ ⊓ stab α₃) : (K ⊓ stab α').relIndex K ≤ 2 := by
  have h2 := Sit43.relIndex_Qv_edge hA h2v h3
  have hQ' : Qv α₃ ≤ stab α' := Qv_le_stab_of_mem_nbrs hA h'
  calc (K ⊓ stab α').relIndex K ≤ (K ⊓ Qv α₃).relIndex K :=
        Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ hQ') (relIndex_ne_zero_of_finite _ _)
    _ = (Qv α₃).relIndex K := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ (Qv α₃).relIndex (stab α₂ ⊓ stab α₃) :=
        Subgroup.relIndex_le_of_le_right hK (by rw [h2]; norm_num)
    _ = 2 := h2

theorem relIndex_Wn_le_four (hA : F53Amalgam H M S) (hs : Sit43 α) (hb4 : bMin H M = 4)
    (h14 : Claim14 α) {α' α₂ α₃ : Geo H M} (hc : IsCritPair₁ α α') (h3 : α₃ ∈ nbrs α₂)
    (h' : α' ∈ nbrs α₃) (d2 : dist α α₂ = 2) (d3 : dist α α₃ = 3) :
    (Wn α ⊓ stab α').relIndex (Wn α) ≤ 4 := by
  have h2v : vtype α₂ = false := hs.vtype_of_dist_two hA (by rw [CosetGeom.dist_comm]; exact d2)
  obtain ⟨hW2, hW3, -⟩ := h14 hc (nbrs_symm h') (by rw [hb4]; exact d3) (nbrs_symm h3)
    (by rw [hb4]; exact d2)
  have hK : Wn α ⊓ stab α₃ ≤ stab α₂ ⊓ stab α₃ := inf_le_inf_right _ hW2
  have h1 := relIndex_inf_le_two hA h2v h3 h' hK
  have hle : Wn α ⊓ stab α₃ ⊓ stab α' ≤ Wn α ⊓ stab α' :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  calc (Wn α ⊓ stab α').relIndex (Wn α) ≤ (Wn α ⊓ stab α₃ ⊓ stab α').relIndex (Wn α) :=
        Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)
    _ = (Wn α ⊓ stab α₃ ⊓ stab α').relIndex (Wn α ⊓ stab α₃) *
          (Wn α ⊓ stab α₃).relIndex (Wn α) :=
        (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left).symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 hW3
    _ = 4 := by norm_num

theorem isSec_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) : IsSec (stab α) (Zv α) (Wn α) where
  le := hs.Zv_le_Wn hA h26
  normN := stab_le_normalizer_Wn α
  normL := stab_le_normalizer_Zv hA α
  comm := fun _ hx _ hy => hs.comm_Wn_le hA h26 hb (Subgroup.commutator_mem_commutator hx hy)
  sq := hs.sq_mem_Zv hA h26 hb

theorem case1_transvec (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb4 : bMin H M = 4) (h14 : Claim14 α) {α' α₂ α₃ δ : Geo H M} (hc : IsCritPair₁ α α')
    (h3 : α₃ ∈ nbrs α₂) (h' : α' ∈ nbrs α₃) (d2 : dist α α₂ = 2) (d3 : dist α α₃ = 3)
    (hδ : δ ∈ nbrs α) {x : G} (hxα : x ∈ stab α) (hx2 : x * x = 1)
    (hxT : (Zv α ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (Zv α) = 2)
    (hxM : x ∉ Mab α δ) (hxH : ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α)
    (htwo : ∀ v₁ ∈ Vn δ, ∀ v₂ ∈ Vn δ, x * v₁ * x⁻¹ * v₁⁻¹ ∉ Zv α →
      x * v₂ * x⁻¹ * v₂⁻¹ ∉ Zv α → (x * v₁ * x⁻¹ * v₁⁻¹)⁻¹ * (x * v₂ * x⁻¹ * v₂⁻¹) ∈ Zv α)
    {E : Subgroup G} (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hZE : Zv α ≤ E)
    (hEW : E ≤ Wn α) (hR : Vn δ ⊓ E = Zv α) (hD4 : Nat.card (Vn δ) = 2 ^ 6)
    (horth : IsOrthSec (stab α) E (Wn α)) : IsTransvec 1 x (Zv α) (Wn α) := by
  have hb : 4 ≤ bMin H M := by omega
  obtain ⟨D⟩ := hs.exists_dict hA hδ
  have hsecZ := isSec_Zv hA h26 hs hb
  have hQ : ⁅Wn α, pCoreOf 2 (stab α)⁆ ≤ Zv α :=
    hs.comm_Wn_Qv_le hA h26 (by omega) hs.vα hδ hD4
  have hsecE := EvenMod.isSec_of_ge hsecZ hZE hEW hE
  have hQE : ⁅Wn α, pCoreOf 2 (stab α)⁆ ≤ E := hQ.trans hZE
  set W := secMod D hsecZ hQ with hWdef
  set WE := secMod D hsecE hQE with hWEdef
  obtain ⟨eO⟩ := iso_orth_of_isOrthSec D hsecE hQE horth
  have := hsecZ.normal_subgroupOf
  have := hsecE.normal_subgroupOf
  let g : W.W →* WE.W :=
    QuotientGroup.map ((Zv α).subgroupOf (Wn α)) (E.subgroupOf (Wn α)) (MonoidHom.id _)
      (fun _ hy => hZE hy)
  have hg : ∀ y : ↥(Wn α), g (secProj D hsecZ hQ y) = secProj D hsecE hQE y := fun _ => rfl
  let π : W.W →* orth.W := eO.toMulEquiv.toMonoidHom.comp g
  have hπ : ∀ y : ↥(Wn α), π (secProj D hsecZ hQ y) = eO.toMulEquiv (secProj D hsecE hQE y) :=
    fun y => by show eO.toMulEquiv (g _) = _; rw [hg]
  have hπs : Function.Surjective π := by
    intro o
    obtain ⟨w, hw⟩ := eO.toMulEquiv.surjective o
    obtain ⟨y, rfl⟩ := secProj_surjective D hsecE hQE w
    exact ⟨secProj D hsecZ hQ y, by rw [hπ, hw]⟩
  have hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w) := by
    intro σ w
    obtain ⟨k, rfl⟩ := D.surj σ
    obtain ⟨y, rfl⟩ := secProj_surjective D hsecZ hQ w
    rw [secMod_act, hπ, hπ, ← eO.map_act, secMod_act]
    rfl
  have hπ1 : ∀ y : ↥(Wn α), π (secProj D hsecZ hQ y) = 1 ↔ (y : G) ∈ E := fun y => by
    rw [hπ, MulEquiv.map_eq_one_iff, secProj_eq_one_iff]
  have hZV : Zv α ≤ Vn δ := Sit43.Zv_le_Vn hδ
  have hVW : Vn δ ≤ Wn α := hs.Vn_le_Wn hA h26 hδ
  set V := secSub D hsecZ hQ (Vn δ) with hVdef
  have hVmem : ∀ y : ↥(Wn α), secProj D hsecZ hQ y ∈ V ↔ (y : G) ∈ Vn δ :=
    mem_secSub_iff D hsecZ hQ hZV
  have hVinj : ∀ v ∈ V, π v = 1 → v = 1 := by
    rintro _ ⟨y, hy, rfl⟩ h1
    rw [hπ1] at h1
    rw [secProj_eq_one_iff, ← hR]
    exact ⟨hy, h1⟩
  have hVT : ∀ σ ∈ S5That, ∀ v ∈ V, W.act σ v = v := by
    rintro σ hσ _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hkα, hkσ⟩ := hs.exists_Qst_of_S5That hA h26 hδ D hσ
    rw [← hkσ, secMod_fix_iff]
    exact hs.comm_Qst_Vn_mem hA h26 hδ hk hy
  have hVS : ∀ σ ∈ S5Syl, ∀ v ∈ V, W.act σ v ∈ V := by
    rintro σ hσ _ ⟨y, hy, rfl⟩
    rw [← D.bar_S] at hσ
    obtain ⟨s, hsS, rfl⟩ := (D.mem_bar_iff σ).mp hσ
    rw [secMod_act, hVmem]
    show (s : G) * y * (s : G)⁻¹ ∈ Vn δ
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hsS.2) y).mp hy
  have hVY : V.map π = fixW orth S5That := by
    have hle : V.map π ≤ fixW orth S5That := by
      rintro _ ⟨v, hv, rfl⟩ σ hσ
      rw [← hπe, hVT σ hσ v hv]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_fixW_orth_S5That]
    have hinj : Function.Injective (π.domRestrict V) := by
      rw [injective_iff_map_eq_one]
      intro v hv
      exact Subtype.ext (hVinj v v.2 hv)
    have h1 : Nat.card (V.map π) = Nat.card V := by
      rw [← MonoidHom.domRestrict_range]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1, card_secSub D hsecZ hQ hVW, hs.relIndex_Zv_Vn hs.vα hδ hD4]
  have hgen : ∀ U : Subgroup W.W, IsInvSub W ⊤ U → V ≤ U → U = ⊤ := by
    intro U hU hVU
    let Ut : Subgroup G := (U.comap (secProj D hsecZ hQ)).map (Wn α).subtype
    have hUt : ∀ y : ↥(Wn α), (y : G) ∈ Ut ↔ secProj D hsecZ hQ y ∈ U := by
      intro y
      constructor
      · rintro ⟨y', hy', hyy'⟩
        have : y' = y := Subtype.ext hyy'
        rw [← this]
        exact hy'
      · intro h
        exact ⟨y, h, rfl⟩
    have hWU : Wn α ≤ Ut := by
      rw [hs.Wn_eq_iSup_conj hA h26 hs.vα hδ]
      refine iSup₂_le fun g hg => ?_
      rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ Wn α := hVW hv
      have hgv : g * v * g⁻¹ ∈ Wn α :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hg) v).mp hvW
      show g * v * g⁻¹ ∈ Ut
      refine (hUt ⟨_, hgv⟩).mpr ?_
      have h1 := hU (D.ψ ⟨g, hg⟩) (Subgroup.mem_top _) _ (hVU ((hVmem ⟨v, hvW⟩).mpr hv))
      rw [secMod_act] at h1
      exact h1
    rw [eq_top_iff]
    intro w _
    obtain ⟨y, rfl⟩ := secProj_surjective D hsecZ hQ w
    exact (hUt y).mp (hWU y.2)
  set t := D.ψ ⟨x, hxα⟩ with ht
  have ht2 : idx orth t = 2 := by rw [ht, ← D.relIndex_centralizer_eq]; exact hxT
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, EvenMod.idx_one] at ht2
    omega
  have htsw : t.IsSwap := ((transvections t ht1).2).mp ht2
  have ht4 : t 4 ≠ 4 := fun h => hxM ((Sit43.mem_Mab_iff D ⟨x, hxα⟩).mpr h)
  have hcomm : ∀ y : ↥(Wn α), W.act t (secProj D hsecZ hQ y) * (secProj D hsecZ hQ y)⁻¹ =
      secProj D hsecZ hQ ⟨x * y * x⁻¹ * (y : G)⁻¹, (Wn α).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hxα) y).mp y.2)
        ((Wn α).inv_mem y.2)⟩ := by
    intro y
    rw [ht, secMod_act, ← map_inv, ← map_mul]
    rfl
  obtain ⟨c, hcc⟩ : ∃ c : W.W, ∀ y : ↥(Wn α), (y : G) ∈ Vn δ →
      W.act t (secProj D hsecZ hQ y) * (secProj D hsecZ hQ y)⁻¹ = 1 ∨
      W.act t (secProj D hsecZ hQ y) * (secProj D hsecZ hQ y)⁻¹ = c := by
    by_cases hall : ∀ v ∈ Vn δ, x * v * x⁻¹ * v⁻¹ ∈ Zv α
    · refine ⟨1, fun y hy => Or.inl ?_⟩
      rw [hcomm, secProj_eq_one_iff]
      exact hall y hy
    · push Not at hall
      obtain ⟨v₁, hv₁, hn₁⟩ := hall
      refine ⟨W.act t (secProj D hsecZ hQ ⟨v₁, hVW hv₁⟩) *
        (secProj D hsecZ hQ ⟨v₁, hVW hv₁⟩)⁻¹, fun y hy => ?_⟩
      by_cases hy1 : x * y * x⁻¹ * (y : G)⁻¹ ∈ Zv α
      · left
        rw [hcomm, secProj_eq_one_iff]
        exact hy1
      · right
        rw [hcomm, hcomm, secProj_eq_iff]
        show (x * y * x⁻¹ * (y : G)⁻¹)⁻¹ * (x * v₁ * x⁻¹ * v₁⁻¹) ∈ Zv α
        have h1 := (Zv α).inv_mem (htwo v₁ hv₁ y hy hn₁ hy1)
        rwa [mul_inv_rev, inv_inv] at h1
  have htt : t * t = 1 := by
    obtain ⟨a, b, -, hab⟩ := htsw
    rw [hab, swap_mul_self]
  have h6 : Nat.card (commW W (Subgroup.zpowers t) V) ≤ 2 := by
    have hle : commW W (Subgroup.zpowers t) V ≤ Subgroup.zpowers c := by
      unfold commW
      rw [Subgroup.closure_le]
      rintro _ ⟨b, hb, _, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := (mem_zpowers_iff_of_pow_eq_one (m := 2)
        (by rw [pow_two]; exact htt) (by norm_num)).mp hb
      interval_cases k
      · simp
      · rw [pow_one]
        rcases hcc y hy with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers c
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact W.sq c)
  have h7 : idx W t ≤ 4 := by
    rw [ht, idx_secMod D hsecZ hQ hxα]
    unfold secIdx
    have hle : Wn α ⊓ stab α' ≤ fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α) := by
      intro h hh
      refine Subgroup.subset_closure ⟨hh.1, fun a ha => ?_⟩
      obtain ⟨k, hk, rfl⟩ := (mem_zpowers_iff_of_pow_eq_one (m := 2)
        (by rw [pow_two]; exact hx2) (by norm_num)).mp ha
      interval_cases k
      · simp
      · rw [pow_one]
        have h1 := (Zv α).inv_mem (hxH h hh)
        rwa [show (h * x * h⁻¹ * x⁻¹)⁻¹ = x * h * x⁻¹ * h⁻¹ by group] at h1
    calc (fixSecIn (Subgroup.zpowers x) (Zv α) (Wn α)).relIndex (Wn α)
        ≤ (Wn α ⊓ stab α').relIndex (Wn α) :=
          Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)
      _ ≤ 4 := relIndex_Wn_le_four hA hs hb4 h14 hc h3 h' d2 d3
  have hidx := case1_module W π hπs hπe V hVinj hVY hVT hVS hgen htsw ht4 h6 h7
  exact (isTransvec_one_iff D hsecZ hQ hxα).mpr hidx

end Sit43'

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
