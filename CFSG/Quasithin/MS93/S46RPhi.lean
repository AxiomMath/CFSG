module

public import CFSG.Quasithin.MS93.S46X3Grp
public import CFSG.Quasithin.MS93.S46I469Loc
public import CFSG.Quasithin.MS93.S46IdxLin

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem eq_zero_of_rot_mulVec_eq [CharP F 2] {v : Fin 3 → F} (h0 : v 0 = 0)
    (h : ((rootElt 1 2 1 * rootElt 2 1 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    rootElt_mulVec (show (2 : Fin 3) ≠ 1 by decide),
    rootElt_mulVec (show (1 : Fin 3) ≠ 2 by decide)] at h
  have h1 : v 1 + (v 2 + v 1) = v 1 := by
    have := congrFun h 1
    simp only [Pi.add_apply, Pi.single_apply, one_mul] at this
    simpa using this
  have h2 : v 2 + v 1 = v 2 := by
    have := congrFun h 2
    simp only [Pi.add_apply, Pi.single_apply, one_mul] at this
    simpa using this
  have hv1 : v 1 = 0 := add_eq_left.mp h2
  have hv2 : v 2 = 0 := by
    have h3 := add_eq_left.mp h1
    rwa [hv1, add_zero] at h3
  funext k
  fin_cases k
  · exact h0
  · exact hv1
  · exact hv2

end Lin

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem exists_lift_rot_vv (d : X3Data c α β γ ψ) :
    ∃ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k = rootElt 1 2 1 * rootElt 2 1 1 ∧
      ∀ x ∈ Vv (puAmalgam c.pu.le) β,
        ⁅x, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZH (puAmalgam c.pu.le) β := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have ha : (1 : F) ≠ 0 := one_ne_zero
  have hB3 : (rootElt 1 2 1 * rootElt 2 1 (1 : F)⁻¹ : SL3 F) ^ 3 = 1 :=
    rootElt12_mul_rootElt21_pow_three ha
  rw [inv_one] at hB3
  obtain ⟨k₀, hk₀⟩ := toSL3_surjective d.lh.surj (rootElt 1 2 1 * rootElt 2 1 (1 : F))
  have h3 : toSL3 ψ (k₀ ^ 3) = 1 := by rw [map_pow, hk₀, hB3]
  obtain ⟨e, he⟩ := pow_two_pow_eq_one_of_toSL3_eq_one c.pu c.via d.mα d.lh.nat _ h3
  have hmod : 2 ^ e * 2 ^ e % 3 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  set k : ↥(stab (puAmalgam c.pu.le) α) := k₀ ^ (2 ^ e * 2 ^ e) with hk
  have hk3 : k ^ 3 = 1 := by
    rw [hk, ← pow_mul, show 2 ^ e * 2 ^ e * 3 = 3 * 2 ^ e * 2 ^ e by ring, pow_mul, pow_mul, he,
      one_pow]
  have hψk : toSL3 ψ k = rootElt 1 2 1 * rootElt 2 1 1 := by
    rw [hk, map_pow, hk₀, pow_eq_pow_mod _ hB3, hmod, pow_one]
  have hodd : Odd (orderOf (k : (puAmalgam c.pu.le).Universal)) := by
    have h1 : (k : (puAmalgam c.pu.le).Universal) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hk3, Subgroup.coe_one]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1) with h | h <;>
      rw [h] <;> decide
  have hN := d.mem_normalizer_qv (k := k) (by
    rw [hψk]
    exact Subgroup.mul_mem _ (rootElt12_mem_normalizer 1) (rootElt21_mem_normalizer 1))
  have hZ : ∀ z ∈ ZM (puAmalgam c.pu.le) α,
      ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZH (puAmalgam c.pu.le) β := by
    intro z hz
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull d.mα hz
    set kk : (puAmalgam c.pu.le).Universal := (k : (puAmalgam c.pu.le).Universal) with hkk
    have hζk : ζ * kk = kk * ζ := (d.lh.comm_z0_k hζ k.2).symm
    have e1 : ⁅u * ζ, kk⁆ = ⁅u, kk⁆ := by
      simp only [commutatorElement_def]
      calc u * ζ * kk * (u * ζ)⁻¹ * kk⁻¹ = u * (ζ * kk) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by group
        _ = u * (kk * ζ) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by rw [hζk]
        _ = u * kk * u⁻¹ * kk⁻¹ := by group
    rw [e1]
    have hmem : ⁅u, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ Uloc c.pu.le L α :=
      I467.commutator_mem_of_natural d.lh.nat ⟨u, hu⟩ k
    have hnat := natVec_commutator d.lh.nat k ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    have hc : natVec d.lh.nat ⟨_, hmem⟩ ∈ commN (natImage ψ (Qv (puAmalgam c.pu.le) β)) := by
      rw [d.qvβ]
      apply mem_commN_of_apply_zero
      rw [hnat, hψk, Pi.sub_apply, rootElt12_mul_rootElt21_mulVec_apply_zero, sub_self]
    have h1 := (mem_commutator_iff_natVec d.lh.nat d.qβK ⟨_, hmem⟩).mpr hc
    rw [← S4A.usup_eq_commutator_uloc c.pu hfull d.mα d.adjαβ] at h1
    exact d.uZ h1
  exact ⟨k, hψk, d.odd (k : (puAmalgam c.pu.le).Universal) k.2 hN hZ hodd⟩

section Cent

variable {𝔾 : Type} [Group 𝔾]

@[expose] def centMod (K C N : Subgroup 𝔾) (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {g | g ∈ K ∧ ∀ y ∈ C, ⁅y, g⁆ ∈ N}
  one_mem' := ⟨K.one_mem, fun y _ => by rw [commutatorElement_one_right]; exact N.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun y hy => by
    have e : ⁅y, g * g'⁆ = ⁅y, g⁆ * (g * ⁅y, g'⁆ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hg.2 y hy) ((Subgroup.mem_normalizer_iff.mp (hKN hg.1) _).mp (hg'.2 y hy))⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun y hy => by
    have e : ⁅y, g⁻¹⁆ = g⁻¹ * ⁅y, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hg.1)) _).mp (N.inv_mem (hg.2 y hy))⟩

theorem mem_centMod {K C N : Subgroup 𝔾} {hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)} {g : 𝔾} :
    g ∈ centMod K C N hKN ↔ g ∈ K ∧ ∀ y ∈ C, ⁅y, g⁆ ∈ N :=
  Iff.rfl

theorem conj_mem_centMod {K C N : Subgroup 𝔾} {hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)}
    (hKC : K ≤ Subgroup.normalizer (C : Set 𝔾)) {k g : 𝔾} (hk : k ∈ K)
    (hg : g ∈ centMod K C N hKN) : k * g * k⁻¹ ∈ centMod K C N hKN := by
  refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk), fun y hy => ?_⟩
  have hy' : k⁻¹ * y * k⁻¹⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hKC (K.inv_mem hk)) y).mp hy
  have e : ⁅y, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * y * k⁻¹⁻¹, g⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp (hg.2 _ hy')

theorem commutator_mul_right_mul_right {a b x y : 𝔾} (ha : Commute a (x * b))
    (hb : Commute b y) : ⁅y * a, x * b⁆ = ⁅y, x⁆ := by
  have h1 : ⁅y * a, x * b⁆ = ⁅y, x * b⁆ := by
    simp only [commutatorElement_def]
    rw [mul_assoc y a (x * b), ha.eq]
    group
  have h2 : b * y⁻¹ = y⁻¹ * b := hb.inv_right.eq
  rw [h1]
  simp only [commutatorElement_def]
  calc y * (x * b) * y⁻¹ * (x * b)⁻¹ = y * x * (b * y⁻¹) * b⁻¹ * x⁻¹ := by group
    _ = y * x * (y⁻¹ * b) * b⁻¹ * x⁻¹ := by rw [h2]
    _ = y * x * y⁻¹ * x⁻¹ := by group

end Cent

theorem le_bloc_of_commutator_qv_le_cfg (h464 : I464) (h467 : I467) (h469 : I469Cfg M T L φ)
    (d : X3Data c α β γ ψ) {C : Subgroup (puAmalgam c.pu.le).Universal}
    (hCV : C ≤ Vv (puAmalgam c.pu.le) α)
    (hCn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (C : Set (puAmalgam c.pu.le).Universal))
    (hCT : ⁅C, Qv (puAmalgam c.pu.le) β⁆ ≤ Bloc c.pu.le L α) : C ≤ Bloc c.pu.le L α := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have hb : 2 < critDist (puAmalgam c.pu.le) := critDist_gt_two c
  have hB := h467 G M T L F φ c α d.mα
  have hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α :=
    (h469 c α β d.mα d.adjαβ).2.1.le
  have hBn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (Bloc c.pu.le L α : Set (puAmalgam c.pu.le).Universal) :=
    stab_le_normalizer_bloc c.pu α
  have hZB : ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L α := zm_le_bloc c.pu hb d.mα
  set S := centMod (stab (puAmalgam c.pu.le) α) C (Bloc c.pu.le L α) hBn with hS
  have hQS : Qv (puAmalgam c.pu.le) α ≤ S := fun q hq =>
    ⟨d.lh.qK hq, fun y hy => hZB (d.lh.vqc (Subgroup.commutator_mem_commutator (hCV hy) hq))⟩
  have hTS : Qv (puAmalgam c.pu.le) β ≤ S := fun t ht =>
    ⟨d.qβK ht, fun y hy => hCT (Subgroup.commutator_mem_commutator hy ht)⟩
  have hSn : (natImage ψ S).Normal := by
    have hsub : (S.subgroupOf (stab (puAmalgam c.pu.le) α)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using conj_mem_centMod hCn g.2 hn
    exact hsub.map _ (toSL3_surjective d.lh.surj)
  have h10 : rootElt 1 0 (1 : F) ∈ natImage ψ S := by
    have hmem : rootElt 1 0 (1 : F) ∈ natImage ψ (Qv (puAmalgam c.pu.le) β) := by
      rw [d.qvβ]
      exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 1)
    obtain ⟨t, ht, he⟩ := mem_natImage.mp hmem
    exact mem_natImage.mpr ⟨t, hTS ht, he⟩
  have htop : natImage ψ S = ⊤ :=
    Idx.eq_top_of_normal_of_mem_rH hSn h10
      (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 1))
      (fun h1 => one_ne_zero ((rootElt_eq_one_iff (show (1 : Fin 3) ≠ 0 by decide) 1).mp h1))
  have hKS : stab (puAmalgam c.pu.le) α ≤ S := d.stab_le_of_natImage_eq_top hQS htop
  obtain ⟨k, hψk, hkV⟩ := exists_lift_rot_vv d
  have hkS := hKS k.2
  have hβH : ¬ IsMVtx (puAmalgam c.pu.le) β := by
    have := isMVtx_iff_of_adj _ d.adjαβ
    have := d.mα
    tauto
  have h464' : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ →
      (puAmalgam c.pu.le).treeGraph.Adj δ ρ → Usup (puAmalgam c.pu.le) δ ρ ≤ ZH _ ρ :=
    fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ
  have hVβα : Vv (puAmalgam c.pu.le) β ≤ Vv (puAmalgam c.pu.le) α := by
    rw [vv_eq_iSup_vv d.mα]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam c.pu.le).treeGraph.neighborSet α) =>
      Vv (puAmalgam c.pu.le) ρ) β d.adjαβ le_rfl
  have hcent : ∀ y ∈ Vv (puAmalgam c.pu.le) α, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      y ∈ Bloc c.pu.le L α → Commute y v := by
    intro y _ v hv hy
    rw [hB] at hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 v hv).symm
  have hCβ : ∀ y ∈ C, ∀ x ∈ Vv (puAmalgam c.pu.le) β, ⁅y, x⁆ = 1 := by
    intro y hy x hx
    have hyV := hCV hy
    have hxV := hVβα hx
    set u := ⁅y, x⁆ with hu
    have huU : u ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hyV hxV)
    have huZ : u ∈ ZH (puAmalgam c.pu.le) β := by
      have h1 : u ∈ ⁅Qv (puAmalgam c.pu.le) β, Vv (puAmalgam c.pu.le) β⁆ :=
        Subgroup.commutator_mem_commutator (d.qαβ (d.lh.vq hyV)) hx
      rw [Subgroup.commutator_comm] at h1
      exact commutator_vv_qv_le_zh c.pu h464' hβH h1
    have hu0 : natVecG d.lh.nat u 0 = 0 := by
      have hmem : rootElt 1 0 (1 : F) ∈ natImage ψ (Qv (puAmalgam c.pu.le) β) := by
        rw [d.qvβ]
        exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 1)
      obtain ⟨t, ht, he⟩ := mem_natImage.mp hmem
      have htu : (t : (puAmalgam c.pu.le).Universal) * u *
          ((t : (puAmalgam c.pu.le).Universal))⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β huZ) _ ht,
          mul_inv_cancel_right]
      have h1 := natVecG_conj d.lh.nat t huU
      rw [htu, he, rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide)] at h1
      have h2 := congrFun h1 1
      simpa using h2
    set kk : (puAmalgam c.pu.le).Universal := (k : (puAmalgam c.pu.le).Universal) with hkk
    have hku : kk * u * kk⁻¹ = u := by
      have hy' : y⁻¹ * (kk * y * kk⁻¹) ∈ Bloc c.pu.le L α := by
        have := hkS.2 y⁻¹ (C.inv_mem hy)
        simp only [commutatorElement_def, inv_inv] at this
        simpa [mul_assoc] using this
      have hx' : x⁻¹ * (kk * x * kk⁻¹) ∈ ZH (puAmalgam c.pu.le) β := by
        have := hkV x⁻¹ (Subgroup.inv_mem _ hx)
        simp only [commutatorElement_def, inv_inv] at this
        simpa [mul_assoc] using this
      set a := y⁻¹ * (kk * y * kk⁻¹) with ha
      set b := x⁻¹ * (kk * x * kk⁻¹) with hb'
      have hbB : b ∈ Bloc c.pu.le L α := hZB (zh_le_zm _ d.adjαβ hx')
      have hbV : b ∈ Vv (puAmalgam c.pu.le) α := by
        have := hbB
        rw [hB] at this
        exact this.1
      have haV : a ∈ Vv (puAmalgam c.pu.le) α := by
        have := hy'
        rw [hB] at this
        exact this.1
      have e1 : kk * y * kk⁻¹ = y * a := by rw [ha, mul_inv_cancel_left]
      have e2 : kk * x * kk⁻¹ = x * b := by rw [hb', mul_inv_cancel_left]
      have e3 : kk * u * kk⁻¹ = ⁅kk * y * kk⁻¹, kk * x * kk⁻¹⁆ := by
        rw [hu]
        simp only [commutatorElement_def]
        group
      rw [e3, e1, e2]
      exact commutator_mul_right_mul_right
        (hcent a haV _ ((Vv (puAmalgam c.pu.le) α).mul_mem hxV hbV) hy')
        (hcent b hbV y hyV hbB)
    have h1 := natVecG_conj d.lh.nat k huU
    rw [hku, hψk] at h1
    have h0 := eq_zero_of_rot_mulVec_eq hu0 h1.symm
    exact natVecG_injective d.lh.nat huU (Subgroup.one_mem _) (by rw [h0, natVecG_one])
  have hCα : Vv (puAmalgam c.pu.le) α ≤
      Subgroup.centralizer (C : Set (puAmalgam c.pu.le).Universal) := by
    rw [vv_eq_iSup_vv d.mα]
    refine iSup₂_le fun β' hβ' => ?_
    obtain ⟨g, hg, rfl⟩ := I467.exists_mem_stab_smul_eq d.mα d.adjαβ hβ'
    have hV : Vv (puAmalgam c.pu.le) (g • β) =
        (Vv (puAmalgam c.pu.le) β).map (MulAut.conj g).toMonoidHom := PU.vi_smul _ g β 2
    rw [hV]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hCn (Subgroup.inv_mem _ hg)) y).mp hy
    have h1 := hCβ _ hy' x hx
    have e : ⁅y, (MulAut.conj g).toMonoidHom x⁆ = g * ⁅g⁻¹ * y * g⁻¹⁻¹, x⁆ * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [h1, mul_one, mul_inv_cancel] at e
    exact commutatorElement_eq_one_iff_mul_comm.mp e
  intro y hy
  rw [hB]
  refine ⟨hCV hy, ?_⟩
  show y ∈ Subgroup.centralizer (Vv (puAmalgam c.pu.le) α : Set (puAmalgam c.pu.le).Universal)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hCα hv) y hy).symm

theorem le_bloc_of_commutator_qv_le (h464 : I464) (h467 : I467) (h469 : I469)
    (d : X3Data c α β γ ψ) {C : Subgroup (puAmalgam c.pu.le).Universal}
    (hCV : C ≤ Vv (puAmalgam c.pu.le) α)
    (hCn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (C : Set (puAmalgam c.pu.le).Universal))
    (hCT : ⁅C, Qv (puAmalgam c.pu.le) β⁆ ≤ Bloc c.pu.le L α) : C ≤ Bloc c.pu.le L α :=
  le_bloc_of_commutator_qv_le_cfg h464 h467 (h469 G M T L F φ) d hCV hCn hCT

end CFSG.Quasithin.MS93.S46R
