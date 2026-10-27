module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Multiplicative

section Split

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private lemma eq_one_of_mem_centralizer_of_center_eq_bot {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private lemma eq_of_conj_eq_of_center_eq_bot {X : Subgroup G} (hX : Subgroup.center X = ⊥)
    {u v : G} (huX : u ∈ X) (hvX : v ∈ X)
    (h : ∀ y ∈ X, u * y * u⁻¹ = v * y * v⁻¹) : u = v := by
  have huvX : u⁻¹ * v ∈ X := X.mul_mem (X.inv_mem huX) hvX
  have huvC : u⁻¹ * v ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * (u⁻¹ * v) = u⁻¹ * (u * y * u⁻¹) * v := by group
      _ = u⁻¹ * (v * y * v⁻¹) * v := by rw [h y hy]
      _ = (u⁻¹ * v) * y := by group
  have h1 : u⁻¹ * v = 1 := eq_one_of_mem_centralizer_of_center_eq_bot hX huvX huvC
  calc u = u * 1 := by group
    _ = u * (u⁻¹ * v) := by rw [← h1]
    _ = v := by group

private lemma mem_centralizer_of_conj_action {X : Subgroup G} {b x : G}
    (hxX : x ∈ X) (h : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * (x⁻¹ * b) = x⁻¹ * (x * y * x⁻¹) * b := by group
    _ = x⁻¹ * (b * y * b⁻¹) * b := by rw [← h y hy]
    _ = (x⁻¹ * b) * y := by group

theorem ggBstar_split_of_inner {B Bs : Subgroup G} (hBs : GGBstar p B Bs) {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∀ b ∈ Bs, ∃ x ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = x * c := by
  intro b hb
  obtain ⟨xb, hxbX, hxbact⟩ := hinner b hb
  have hxbCBs : xb ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    obtain ⟨x', hx'X, hx'act⟩ := hinner b' hb'
    have hxx' : xb * x' = x' * xb := by
      refine eq_of_conj_eq_of_center_eq_bot hX (X.mul_mem hxbX hx'X) (X.mul_mem hx'X hxbX) ?_
      intro y hy
      have hy1X : x' * y * x'⁻¹ ∈ X := X.mul_mem (X.mul_mem hx'X hy) (X.inv_mem hx'X)
      have hy2X : b' * y * b'⁻¹ ∈ X := by rw [hx'act y hy]; exact hy1X
      have hy3X : xb * y * xb⁻¹ ∈ X := X.mul_mem (X.mul_mem hxbX hy) (X.inv_mem hxbX)
      calc (xb * x') * y * (xb * x')⁻¹
          = xb * (x' * y * x'⁻¹) * xb⁻¹ := by group
        _ = xb * (b' * y * b'⁻¹) * xb⁻¹ := by rw [← hx'act y hy]
        _ = b * (b' * y * b'⁻¹) * b⁻¹ := by rw [← hxbact _ hy2X]
        _ = (b * b') * y * (b * b')⁻¹ := by group
        _ = (b' * b) * y * (b' * b)⁻¹ := by rw [IsElemAbelian.comm hBs.2.1 hb hb']
        _ = b' * (b * y * b⁻¹) * b'⁻¹ := by group
        _ = b' * (xb * y * xb⁻¹) * b'⁻¹ := by rw [hxbact y hy]
        _ = x' * (xb * y * xb⁻¹) * x'⁻¹ := by rw [hx'act _ hy3X]
        _ = (x' * xb) * y * (x' * xb)⁻¹ := by group
    have hc'C : x'⁻¹ * b' ∈ Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_conj_action hx'X hx'act
    have hc'comm : xb * (x'⁻¹ * b') = (x'⁻¹ * b') * xb :=
      Subgroup.mem_centralizer_iff.mp hc'C xb hxbX
    have hxb_b' : xb * b' = b' * xb := by
      calc xb * b' = xb * (x' * (x'⁻¹ * b')) := by group
        _ = (xb * x') * (x'⁻¹ * b') := by group
        _ = (x' * xb) * (x'⁻¹ * b') := by rw [hxx']
        _ = x' * (xb * (x'⁻¹ * b')) := by group
        _ = x' * ((x'⁻¹ * b') * xb) := by rw [hc'comm]
        _ = (x' * (x'⁻¹ * b')) * xb := by group
        _ = b' * xb := by group
    exact hxb_b'.symm
  have hcC : xb⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    mem_centralizer_of_conj_action hxbX hxbact
  have hcomm_xc : xb * (xb⁻¹ * b) = (xb⁻¹ * b) * xb :=
    Subgroup.mem_centralizer_iff.mp hcC xb hxbX
  have hbp : b ^ p = xb ^ p * (xb⁻¹ * b) ^ p := by
    conv_lhs => rw [show b = xb * (xb⁻¹ * b) by group]
    exact Commute.mul_pow hcomm_xc p
  have hbp1 : b ^ p = 1 := hBs.2.1.2 b hb
  have hcCpow : (xb⁻¹ * b) ^ p ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).pow_mem hcC p
  have hxbpC : xb ^ p ∈ Subgroup.centralizer (X : Set G) := by
    have hmul : xb ^ p * (xb⁻¹ * b) ^ p = 1 := by rw [← hbp, hbp1]
    rw [mul_eq_one_iff_eq_inv.mp hmul]
    exact (Subgroup.centralizer (X : Set G)).inv_mem hcCpow
  have hxbp1 : xb ^ p = 1 :=
    eq_one_of_mem_centralizer_of_center_eq_bot hX (X.pow_mem hxbX p) hxbpC
  have hxbBs : xb ∈ Bs := hBs.2.2.2 xb hxbCBs hxbp1
  refine ⟨xb, ⟨hxbBs, hxbX⟩, xb⁻¹ * b, ⟨?_, hcC⟩, ?_⟩
  · exact Bs.mul_mem (Bs.inv_mem hxbBs) hb
  · group

theorem card_ggBstar_split {B Bs : Subgroup G} (hBs : GGBstar p B Bs) {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Nat.card Bs = Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let f : ↥(Bs ⊓ X) × ↥(Bs ⊓ C) → ↥Bs :=
    fun q => ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨x, hx⟩, ⟨c, hc⟩⟩ ⟨⟨x', hx'⟩, ⟨c', hc'⟩⟩ h
    have h' : x * c = x' * c' := by
      have := congrArg Subtype.val h
      simpa [f] using this
    have hxX : x ∈ X := hx.2
    have hx'X : x' ∈ X := hx'.2
    have hcC : c ∈ C := hc.2
    have hc'C : c' ∈ C := hc'.2
    have hz_eq : x'⁻¹ * x = c' * c⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * c) * c⁻¹ := by group
        _ = x'⁻¹ * (x' * c') * c⁻¹ := by rw [h']
        _ = c' * c⁻¹ := by group
    have hzX : x'⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx'X) hxX
    have hzC : x'⁻¹ * x ∈ C := by
      rw [hz_eq]
      exact C.mul_mem hc'C (C.inv_mem hcC)
    have hz1 : x'⁻¹ * x = 1 := eq_one_of_mem_centralizer_of_center_eq_bot hX hzX hzC
    have hxeq : x = x' := (inv_mul_eq_one.mp hz1).symm
    have hceq : c = c' := by
      apply mul_left_cancel (a := x)
      rw [← hxeq] at h'
      exact h'
    apply Prod.ext
    · exact Subtype.ext hxeq
    · exact Subtype.ext hceq
  have hf_surj : Function.Surjective f := by
    intro b
    obtain ⟨x, hx, c, hc, hbc⟩ := ggBstar_split_of_inner hBs hX hnorm hinner b.1 b.2
    exact ⟨(⟨x, hx⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩
  have hcard : Nat.card (↥(Bs ⊓ X) × ↥(Bs ⊓ C)) = Nat.card ↥Bs :=
    Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩
  rw [Nat.card_prod] at hcard
  exact hcard.symm

theorem card_le_of_isElemAbelian_of_cyclic (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcyc : IsCyclic E) : Nat.card E ≤ p := by
  haveI : IsCyclic E := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    simpa using hE.2 (g : G) g.2
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hcard : Nat.card E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  rw [hcard]
  exact Nat.le_of_dvd hp.pos hdvd

theorem GGConfig.card_bstar_centralizer_le {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hE : IsElemAbelian p (Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    IsElemAbelian.mono hcfg.2.1.2.1 inf_le_left
  exact card_le_of_isElemAbelian_of_cyclic hp hE
    (hS.2.2.2.2 _ inf_le_right (IsElemAbelian.isPGroup hE))

theorem GGConfig.card_bstar_inf_centralizer_J_le {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 := by
  set H : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G) with hH
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBH : B ⊓ H = D := by rw [hH, hD, ← inf_assoc, inf_eq_left.mpr hBBs]
  have h1 := Subgroup.relIndex_mul_card B H
  have h2 := Subgroup.relIndex_mul_card B Bs
  rw [inf_eq_left.mpr hBBs] at h2
  have hBs : Nat.card Bs ≤ p * Nat.card B := hcfg.2.1.2.2.1
  have hidx : B.relIndex Bs ≤ p := by
    rw [← h2] at hBs
    exact Nat.le_of_mul_le_mul_right hBs Nat.card_pos
  have hne : B.relIndex Bs ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := Bs)).ne' h2.symm
  have hle : B.relIndex H ≤ B.relIndex Bs := Subgroup.relIndex_le_of_le_right inf_le_left hne
  rw [hBH, hcfg.2.2.1.2.2.1] at h1
  calc Nat.card H = B.relIndex H * p ^ 2 := h1.symm
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (hle.trans hidx)
    _ = p ^ 3 := by ring

theorem GGConfig.B_lt_Bs_of_centralizer_J_card {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hcard : p ^ 2 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))) : B < Bs := by
  apply lt_of_le_of_ne hcfg.2.1.1
  intro hEq
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  rw [← hEq, ← hD, hDcard] at hcard
  exact (lt_irrefl _ hcard)

theorem ggBs_coord_eq_one_of_mem_bCoordinateBlock
    {p n : ℕ} {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0) :
    ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 := by
  have hfix : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      u (eta ⟨x, hxBs⟩) = eta ⟨x, hxBs⟩ := by
    rintro u ⟨φ, hφ, rfl⟩
    obtain ⟨m, hmL, -, hmφ⟩ := mem_ggAutomizer_iff.mp hφ
    have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      apply Subtype.ext
      rw [hmφ ⟨x, hxBs⟩]
      change m * x * m⁻¹ = x
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hLx hmL)]
      group
    simpa [MulAut.congr_apply, MulEquiv.symm_apply_apply, hφx]
  have h := hfix
  rw [hLeta] at h
  exact (forall_bCoordinateBlock_fix_iff hp hp2 i0 (eta ⟨x, hxBs⟩)).mp h

theorem ggBs_mem_iff_coord_eq_one_of_bCoordinateBlock
    {p n : ℕ} {Bs L : Subgroup G} {x : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBsEA : IsElemAbelian p Bs)
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (i0 : Fin n)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0) :
    ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let xbs : ↥Bs := ⟨x, hxBs⟩
  have hxbs_ne : xbs ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hnegInv : ∀ v : Fin n → Multiplicative (ZMod p), v i0 = 1 →
      negOff (p := p) i0 v = v⁻¹ := by
    intro v hv
    funext k
    rw [negOff_apply, Pi.inv_apply]
    by_cases hk : k = i0
    · subst hk
      rw [if_pos rfl, hv]
      exact (inv_one (G := Multiplicative (ZMod p))).symm
    · rw [if_neg hk]
      rfl
  let ν : MulAut ↥Bs := (MulAut.congr eta).symm (negOff (p := p) i0)
  have hν_eq : MulAut.congr eta ν = negOff (p := p) i0 :=
    MulEquiv.apply_symm_apply (MulAut.congr eta) _
  have hν_mem : ν ∈ ggAutomizer L Bs := by
    have hneg : negOff (p := p) i0 ∈
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
      rw [hLeta]
      exact negOff_mem_bCoordinateBlock i0
    obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hneg
    have hφν : φ = ν := by
      apply (MulAut.congr eta).injective
      simpa using hφeq.trans hν_eq.symm
    simpa [hφν] using hφ
  obtain ⟨l, hlL, hlN, hlact⟩ := mem_ggAutomizer_iff.mp hν_mem
  have hνc : ∀ c : ↥Bs, eta c i0 = 1 → ν c = c⁻¹ := by
    intro c hc
    apply eta.injective
    have h1 : eta (ν c) = negOff (p := p) i0 (eta c) := by
      have h := congrArg
        (fun f : MulAut (Fin n → Multiplicative (ZMod p)) => f (eta c)) hν_eq
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        using h
    rw [h1, hnegInv (eta c) hc]
    exact (map_inv eta c).symm
  have hker : ∀ c : ↥Bs, eta c i0 = 1 → (c : G) ∈ L := by
    intro c hc
    have hconj_c : l * (c : G) * l⁻¹ = (c : G)⁻¹ := by
      have h := hlact c
      rw [hνc c hc] at h
      simpa using h.symm
    have hcl : (c : G) * l * (c : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hN c.2) l).mp hlL
    have hcl_inv : (c : G) * l⁻¹ * (c : G)⁻¹ ∈ L := by
      have h := L.inv_mem hcl
      simpa [mul_inv_rev, mul_assoc] using h
    have hcomm : l * (c : G) * l⁻¹ * (c : G)⁻¹ ∈ L := by
      have h := L.mul_mem hlL hcl_inv
      simpa [mul_assoc] using h
    rw [hconj_c] at hcomm
    have hcp : (c : G) ^ p = 1 := by
      simpa using hBsEA.2 c c.2
    have hcsq : (c : G) ^ 2 ∈ L := by
      simpa only [mul_inv_rev, inv_inv, pow_two] using L.inv_mem hcomm
    have hcop : Nat.Coprime 2 (orderOf (c : G)) :=
      Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hcp)
        (hp.odd_of_ne_two hp2).coprime_two_left
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    simpa only [hm] using L.pow_mem hcsq m
  have hxcoord : ∀ k, k ≠ i0 → eta xbs k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock hp hp2 hxBs hLx eta i0 hLeta
  have hui : eta xbs i0 ≠ 1 := by
    intro h0
    have hfun : eta xbs = 1 := by
      funext k
      by_cases hk : k = i0
      · rw [hk]
        simpa using h0
      · rw [hxcoord k hk]
        rfl
    exact hxbs_ne (eta.injective (by simpa using hfun))
  have hs_ne : toAdd (eta xbs i0) ≠ 0 := by
    intro h
    apply hui
    exact toAdd.injective (by simpa using h)
  intro b
  constructor
  · intro hbL
    by_contra hbcoord
    let k : ℕ := (toAdd (eta b i0) / toAdd (eta xbs i0)).val
    have hk : (eta xbs i0) ^ k = eta b i0 := by
      apply toAdd.injective
      rw [toAdd_pow, nsmul_eq_mul]
      dsimp only [k]
      rw [ZMod.natCast_zmod_val]
      exact div_mul_cancel₀ _ hs_ne
    let w : ↥Bs := b * (xbs ^ k)⁻¹
    have hw : eta w i0 = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, map_pow]
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
      rw [hk]
      exact mul_inv_cancel (eta b i0)
    have hwL : (w : G) ∈ L := hker w hw
    have hxpowL : ((xbs ^ k : ↥Bs) : G) ∈ L := by
      have hb_eq : (w : G) * ((xbs ^ k : ↥Bs) : G) = (b : G) := by
        simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h1 : (w : G)⁻¹ * (b : G) ∈ L := L.mul_mem (L.inv_mem hwL) hbL
      have h2 : (w : G)⁻¹ * (b : G) = ((xbs ^ k : ↥Bs) : G) := by
        rw [← hb_eq]
        group
      rwa [h2] at h1
    have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
    have hxpowC : ((xbs ^ k : ↥Bs) : G) ∈ Subgroup.centralizer (L : Set G) := by
      simpa only [Subgroup.coe_pow] using
        (Subgroup.centralizer (L : Set G)).pow_mem hxC k
    have hxpow1 : xbs ^ k = 1 := Subtype.ext
      (eq_one_of_mem_centralizer_of_center_eq_bot hZ hxpowL hxpowC)
    apply hbcoord
    rw [← hk]
    simpa only [map_pow, Pi.pow_apply, map_one, Pi.one_apply] using
      congrArg (fun c : ↥Bs => eta c i0) hxpow1
  · exact hker b

theorem ggBstar_mem_iff_coord_eq_one {n : ℕ} {B Bs L D J : Subgroup G} {x : G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (i0 : Fin n)
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0) :
    ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) := by
  obtain ⟨hp, hBsEA, hxBs, hLx, -⟩ := hcfg.tableB_facts
  exact ggBs_mem_iff_coord_eq_one_of_bCoordinateBlock hp (by decide) hBsEA hxBs
    hcfg.1.2.2.2.2.2.2.1.2.2.1 hLx hZ hN eta i0 hLeta

end Split

end CFSG.StandardType
