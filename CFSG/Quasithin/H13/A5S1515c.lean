module

public import CFSG.Quasithin.H13.A5S1515b
public import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

section General

variable {M : Type*} [Group M]

theorem braid_of_cube {a b : M} (ha : a * a = 1) (hb : b * b = 1) (h3 : (a * b) ^ 3 = 1) :
    b * (a * b) = a * (b * a) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have h1 : a * b * (a * b) = b * a := by
    have : a * b * (a * b) * (a * b) = 1 := by rw [← pow_three']; exact h3
    rw [eq_inv_of_mul_eq_one_left this, mul_inv_rev, hai, hbi]
  calc b * (a * b) = (a * a) * (b * (a * b)) := by rw [ha, one_mul]
    _ = a * (a * b * (a * b)) := by group
    _ = a * (b * a) := by rw [h1]

theorem inSA_swap {t₁ t₂ x : MulAut (Multiplicative V4)} (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1)
    (h3 : (t₁ * t₂) ^ 3 = 1) (h : InSA t₂ t₁ x) : InSA t₁ t₂ x := by
  unfold InSA at h ⊢
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.trans (braid_of_cube h1 h2 h3))))))

theorem sq_comm_of_normalizes {a c : M} (h3 : c ^ 3 = 1)
    (h : a * c = c * a ∨ a * c = c * c * a) : a * a * c = c * (a * a) := by
  rcases h with h | h
  · calc a * a * c = a * (a * c) := by group
      _ = a * (c * a) := by rw [h]
      _ = (a * c) * a := by group
      _ = (c * a) * a := by rw [h]
      _ = c * (a * a) := by group
  · have h3' : c * c * c = 1 := by rw [← pow_three']; exact h3
    have e : a * c * a⁻¹ = c * c := by rw [h]; group
    have : a * a * c * (a * a)⁻¹ = c := by
      calc a * a * c * (a * a)⁻¹ = a * (a * c * a⁻¹) * a⁻¹ := by group
        _ = a * (c * c) * a⁻¹ := by rw [e]
        _ = (a * c * a⁻¹) * (a * c * a⁻¹) := by group
        _ = c * c * (c * c) := by rw [e]
        _ = c * c * c * c := by group
        _ = c := by rw [h3', one_mul]
    exact mul_inv_eq_iff_eq_mul.mp this

end General

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_sq_mem {H Y T : Subgroup G}
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hsq : ∀ x ∈ H, x ^ 2 ∈ Y)
    (hT : IsSylowTwoOf T H) : H ≤ Y ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (Y.subgroupOf H).Normal := ⟨fun y hy h => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hHY h.2) y).mp hy
    simpa using this⟩
  have hp : IsPGroup 2 (↥H ⧸ Y.subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq x x.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  set K := Y.subgroupOf H ⊔ T.subgroupOf H
  have hYi : (Y.subgroupOf H).index = 2 ^ n := hn
  have h1 : K.index ∣ 2 ^ n := by
    rw [← hYi]
    exact Subgroup.index_dvd_of_le le_sup_left
  have h2 : K.index ∣ (T.subgroupOf H).index := Subgroup.index_dvd_of_le le_sup_right
  have hK1 : K.index = 1 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases m with _ | m
    · simpa using hm
    · exfalso
      apply hT.2.2
      rw [hm] at h2
      exact (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans h2
  have hKtop := Subgroup.index_eq_one.1 hK1
  intro x hx
  have hxK : (⟨x, hx⟩ : ↥H) ∈ K := hKtop ▸ Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem H.subtype hxK
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at this
  exact (sup_le_sup (inf_le_left : Y ⊓ H ≤ Y) (inf_le_left : T ⊓ H ≤ T)) this

end Sylow

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Pf1515

variable {S : Setting G T L V} {H : Subgroup G} (P : Pf1515 S H)
include P

theorem t21_props : P.t2 * P.t1 ≠ 1 ∧ (P.t2 * P.t1) ^ 3 = 1 := by
  have e : P.t2 * P.t1 = (P.t1 * P.t2)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left P.t1_props.2.2.1,
      inv_eq_of_mul_eq_one_left P.t2_props.2.2.1]
  rw [e, inv_pow, P.t12_props.2, inv_one]
  exact ⟨fun h => P.t12_props.1 (inv_eq_one.1 h), rfl⟩

theorem inSA_mem {x : MulAut (Multiplicative V4)} (hx : InSA P.t1 P.t2 x) :
    ∃ y : ↥H, (y : G) ∈ V ⊔ conjSub P.g⁻¹ V ∧ P.Φ y = x := by
  have ha : P.v ∈ V ⊔ conjSub P.g⁻¹ V := le_sup_left (a := V) P.v_mem
  have hb : P.g⁻¹ * P.v * P.g ∈ V ⊔ conjSub P.g⁻¹ V :=
    le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem
  set a : ↥H := ⟨P.v, P.v_mem_H⟩ with hadef
  set b : ↥H := ⟨P.g⁻¹ * P.v * P.g, P.v'_mem_H⟩ with hbdef
  have hta : P.t1 = P.Φ a := rfl
  have htb : P.t2 = P.Φ b := rfl
  unfold InSA at hx
  rw [hta, htb] at hx
  rcases hx with h | h | h | h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h, map_one]⟩
  · exact ⟨a, ha, h.symm⟩
  · exact ⟨b, hb, h.symm⟩
  · exact ⟨a * b, Subgroup.mul_mem _ ha hb, by rw [h, map_mul]⟩
  · exact ⟨b * a, Subgroup.mul_mem _ hb ha, by rw [h, map_mul]⟩
  · exact ⟨a * (b * a), Subgroup.mul_mem _ ha (Subgroup.mul_mem _ hb ha),
      by rw [h, map_mul, map_mul]⟩

theorem Q_le_I : pCoreOf 2 H ≤ V ⊔ conjSub P.g⁻¹ V := P.Q_eq_U ▸ P.U_le_I

theorem mem_I_of_Φ_eq {x y : ↥H} (hy : (y : G) ∈ V ⊔ conjSub P.g⁻¹ V) (h : P.Φ x = P.Φ y) :
    (x : G) ∈ V ⊔ conjSub P.g⁻¹ V := by
  have hq := P.Q_le_I ((P.Φ_eq_iff x y).1 h)
  have := (V ⊔ conjSub P.g⁻¹ V).mul_mem hq hy
  simpa using this

theorem conj_mem_I (x : ↥H) {s : ↥H} (hs : P.Φ s = P.t1 ∨ P.Φ s = P.t2) :
    (x : G) * s * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
  have hc : P.ch ∈ Oq ∧ P.ch ≠ 1 ∧ P.ch ^ 3 = 1 := P.ch_props
  have hcases : InSA P.t1 P.t2 (P.Φ x * P.Φ s * (P.Φ x)⁻¹) := by
    rcases hs with hs | hs
    · rw [hs]
      exact normalizes_S3_aut hc.1 P.t1_props.1 P.t2_props.1 (P.Φ_mem x) hc.2
        P.t1_props.2 P.t2_props.2 P.t12_props (P.Φ_normalizes x)
    · rw [hs]
      exact inSA_swap P.t1_props.2.2.1 P.t2_props.2.2.1 P.t12_props.2
        (normalizes_S3_aut hc.1 P.t2_props.1 P.t1_props.1 (P.Φ_mem x) hc.2
          P.t2_props.2 P.t1_props.2 P.t21_props (P.Φ_normalizes x))
  obtain ⟨y, hyI, hy⟩ := P.inSA_mem hcases
  exact P.mem_I_of_Φ_eq (x := x * s * x⁻¹) hyI (by rw [map_mul, map_mul, map_inv, hy])

theorem I_normal : H ≤ Subgroup.normalizer ((V ⊔ conjSub P.g⁻¹ V : Subgroup G) : Set G) := by
  have hQI := P.Q_le_I
  have hNQ : ∀ x ∈ H, ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ ∈ pCoreOf 2 H := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) q).mp hq
  have hV : ∀ x : ↥H, ∀ w ∈ V, (x : G) * w * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
    intro x w hw
    rcases P.V_cases hw with h | h
    · exact hQI (hNQ x x.2 w h)
    · have h1 := hQI (hNQ x x.2 _ h)
      have h2 : (x : G) * P.v * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        P.conj_mem_I x (s := ⟨P.v, P.v_mem_H⟩) (Or.inl rfl)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem h1 h2
      have e : (x : G) * (w * P.v⁻¹) * (x : G)⁻¹ * ((x : G) * P.v * (x : G)⁻¹) =
          (x : G) * w * (x : G)⁻¹ := by group
      rwa [e] at this
  have hV' : ∀ x : ↥H, ∀ w ∈ conjSub P.g⁻¹ V,
      (x : G) * w * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V := by
    intro x w hw
    have hw2 := hw
    rw [mem_conjSub, inv_inv] at hw2
    have hgi := H.inv_mem P.g_mem
    rcases P.V_cases hw2 with h | h
    · have hwQ : w ∈ pCoreOf 2 H := by
        have := hNQ _ hgi _ h
        simpa [mul_assoc] using this
      exact hQI (hNQ x x.2 w hwQ)
    · have hwQ : w * (P.g⁻¹ * P.v * P.g)⁻¹ ∈ pCoreOf 2 H := by
        have := hNQ _ hgi _ h
        have e : P.g⁻¹ * (P.g * w * P.g⁻¹ * P.v⁻¹) * P.g⁻¹⁻¹ = w * (P.g⁻¹ * P.v * P.g)⁻¹ := by
          group
        rwa [e] at this
      have h1 := hQI (hNQ x x.2 _ hwQ)
      have h2 : (x : G) * (P.g⁻¹ * P.v * P.g) * (x : G)⁻¹ ∈ V ⊔ conjSub P.g⁻¹ V :=
        P.conj_mem_I x (s := ⟨_, P.v'_mem_H⟩) (Or.inr rfl)
      have := (V ⊔ conjSub P.g⁻¹ V).mul_mem h1 h2
      have e : (x : G) * (w * (P.g⁻¹ * P.v * P.g)⁻¹) * (x : G)⁻¹ *
          ((x : G) * (P.g⁻¹ * P.v * P.g) * (x : G)⁻¹) = (x : G) * w * (x : G)⁻¹ := by group
      rwa [e] at this
  refine le_normalizer_of_conj_mem fun x hx y hy => ?_
  have hmap : (V ⊔ conjSub P.g⁻¹ V).map (MulAut.conj x).toMonoidHom ≤ V ⊔ conjSub P.g⁻¹ V := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hV ⟨x, hx⟩ w hw
    · rintro _ ⟨w, hw, rfl⟩
      exact hV' ⟨x, hx⟩ w hw
  exact hmap ⟨y, hy, rfl⟩

theorem centralizer_le_Φ {b : MulAut (Multiplicative V4)} (hb : b ∈ Oq)
    (hbc : b * P.ch = P.ch * b) :
    ∃ x : ↥H, (x : G) ∈ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) ∧ P.Φ x = b := by
  have hc := P.ch_props
  have hcube : P.ch * P.ch * P.ch = 1 := by rw [← pow_three']; exact hc.2.2
  have hcL : (P.c : G) ∈ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_left (a := S.L1) P.c_mem
  have hIY : V ⊔ conjSub P.g⁻¹ V ≤ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_right
  rcases centralizer_S3_aut hc.1 P.t1_props.1 P.t2_props.1 hb hc.2 P.t1_props.2
    P.t2_props.2 P.t12_props hbc with h | h | h
  · obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    exact ⟨y, hIY hyI, hy⟩
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    refine ⟨⟨P.c, P.c_mem_H⟩ * y, Subgroup.mul_mem _ hcL (hIY hyI), ?_⟩
    rw [map_mul, hy]
    show P.ch * (P.ch * P.ch * b) = b
    calc P.ch * (P.ch * P.ch * b) = P.ch * P.ch * P.ch * b := by group
      _ = b := by rw [hcube, one_mul]
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    refine ⟨⟨P.c, P.c_mem_H⟩ * ⟨P.c, P.c_mem_H⟩ * y,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcL hcL) (hIY hyI), ?_⟩
    rw [map_mul, map_mul, hy]
    show P.ch * P.ch * (P.ch * b) = b
    calc P.ch * P.ch * (P.ch * b) = P.ch * P.ch * P.ch * b := by group
      _ = b := by rw [hcube, one_mul]

theorem H_eq_gen : H = S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V) ⊔ T := by
  apply le_antisymm
  · refine le_sup_of_sq_mem (B2F.le_normalizer_sup P.hn P.I_normal)
      (fun x hx => ?_) P.hF.sylow_H
    have hsq := sq_comm_of_normalizes P.ch_props.2.2 (P.Φ_normalizes ⟨x, hx⟩)
    rw [← map_mul] at hsq
    obtain ⟨y, hyY, hy⟩ := P.centralizer_le_Φ (P.Φ_mem _) hsq
    have hq := (P.Φ_eq_iff _ _).1 hy.symm
    have h1 := (le_sup_right : V ⊔ conjSub P.g⁻¹ V ≤ S.L1 ⊔ (V ⊔ conjSub P.g⁻¹ V))
      (P.Q_le_I hq)
    have := Subgroup.mul_mem _ h1 hyY
    rw [pow_two]
    simpa using this
  · exact sup_le (sup_le P.L1_le_H P.I_le_H) P.T_le_H

theorem dvd_card_range : 18 ∣ Nat.card P.Φ.range := by
  rw [← card_centralizer_aut P.ch_props.1 P.ch_props.2]
  refine Subgroup.card_dvd_of_le fun b hb => ?_
  obtain ⟨x, -, hx⟩ := P.centralizer_le_Φ hb.1 (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  exact ⟨x, hx⟩

theorem z_central (u : G) (hu : u ∈ conjClosure S.V3 H) : S.z * u = u * S.z :=
  (P.comm_z (P.U_le_Q.trans (pCoreOf_le 2 H) hu)).symm

theorem center_Q : centerOf (pCoreOf 2 H) = S.V1 := by
  rw [P.Q_eq_U]
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    refine P.mem_V1_of_central hx fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp hxc u hu).symm
  · intro x hx
    have hxU : x ∈ conjClosure S.V3 H := le_conjClosure S.V3 H (S.V1_le_V3 hx)
    refine ⟨hxU, ?_⟩
    show x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases S.mem_V1.1 hx with rfl | rfl
    · simp
    · exact (P.z_central u hu).symm

theorem G1_mem_Hz : S.G1 ∈ S.Hz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨P.hH.1.1.trans P.hH.2.1, fun h => ?_⟩, le_rfl, fun h => P.hH.2.2 (P.hH.2.1.trans h)⟩
  have hV1 : S.V1 ≤ pCoreOf 2 S.G1 := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ (S.isPGroup_V.to_le S.V1_le_V)
    · rw [← S.centralizer_V1]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases S.mem_V1.1 hx with rfl | rfl <;> rcases S.mem_V1.1 hy with rfl | rfl <;> simp
    · rw [S.G1_eq_normalizer]
  rw [h, le_bot_iff] at hV1
  have := S.card_V1
  rw [hV1] at this
  simp at this

theorem H_eq_G1 : H = S.G1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG1 := P.G1_mem_Hz
  have hF1 := S.hypF91 P.h1323 hG1
  have hHG1 : H ≤ S.G1 := P.hH.2.1
  have hTG1 : T ≤ S.G1 := P.T_le_H.trans hHG1
  have hQ1T : pCoreOf 2 S.G1 ≤ T := by
    obtain ⟨P', hP'⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
    have := pCoreOf_two_le_sylow S.G1 P' (hP' ▸ hTG1)
    rwa [hP'] at this
  have hQ1Q : pCoreOf 2 S.G1 ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hQ1T.trans P.T_le_H)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hUU1 : conjClosure S.V3 H ≤ conjClosure S.V3 S.G1 := conjClosure_mono le_rfl hHG1
  have hU1Q1 : conjClosure S.V3 S.G1 ≤ pCoreOf 2 S.G1 := hF1.conjClosure_Vp_le_pCoreOf
  have hQ1 : pCoreOf 2 S.G1 = conjClosure S.V3 H :=
    le_antisymm (hQ1Q.trans P.Q_eq_U.le) (hUU1.trans hU1Q1)
  have hU1 : conjClosure S.V3 S.G1 = conjClosure S.V3 H :=
    le_antisymm (hU1Q1.trans hQ1.le) hUU1
  have hG1N : S.G1 ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    hQ1 ▸ le_normalizer_pCoreOf 2 S.G1
  have hG1z : S.G1 ≤ Subgroup.centralizer ({P.C.z} : Set G) := by rw [P.Cz]; exact le_rfl
  have hker1 : (P.C.act S.G1 hG1N hG1z).ker = (pCoreOf 2 S.G1).subgroupOf S.G1 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Q8Coords.act_eq_one_iff, hF1.F92_3.1, hU1,
      mem_centralizerMod]
    constructor
    · intro h
      refine ⟨x.2, hF1.H_normalizes_V₁ x.2, fun u hu => ?_⟩
      rw [S.mem_V1, ← P.Cz]
      exact h u hu
    · intro h u hu
      have := h.2.2 u hu
      rwa [S.mem_V1, ← P.Cz] at this
  have hcard1 : Nat.card S.G1 =
      Nat.card (pCoreOf 2 S.G1) * Nat.card (P.C.act S.G1 hG1N hG1z).range := by
    rw [← Subgroup.card_mul_index ((pCoreOf 2 S.G1).subgroupOf S.G1), ← hker1,
      Subgroup.index_ker, hker1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 S.G1)).toEquiv
  have hrange1 : Nat.card (P.C.act S.G1 hG1N hG1z).range ∣ 72 := by
    rw [← card_Oq]
    exact Subgroup.card_dvd_of_le fun b ⟨x, hx⟩ => hx ▸ P.C.act_mem_Oq _ _ _ x
  have hkerH : P.Φ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, P.Φ_eq_one_iff]
  have hcardH : Nat.card H = Nat.card (pCoreOf 2 H) * Nat.card P.Φ.range := by
    rw [← Subgroup.card_mul_index ((pCoreOf 2 H).subgroupOf H), ← hkerH,
      Subgroup.index_ker, hkerH]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).toEquiv
  have hQeq : Nat.card (pCoreOf 2 S.G1) = Nat.card (pCoreOf 2 H) := by
    rw [hQ1, P.Q_eq_U]
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  obtain ⟨k, hk⟩ := P.dvd_card_range
  obtain ⟨m, hm⟩ := hrange1
  have hidx := Subgroup.card_mul_index (H.subgroupOf S.G1)
  have hHcard : Nat.card ↥(H.subgroupOf S.G1) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG1).toEquiv
  rw [hHcard] at hidx
  have hodd : ¬ 2 ∣ (H.subgroupOf S.G1).index := by
    intro h2
    have hT := isSylowTwoOf_of_le S.h13.sylow hTG1
    apply hT.2.2
    exact h2.trans (Subgroup.index_dvd_of_le fun x hx => P.T_le_H hx)
  generalize hn : (H.subgroupOf S.G1).index = n at hidx hodd
  have h4 : n ∣ 4 := by
    have e1 : Nat.card (pCoreOf 2 H) * (18 * k * n * m) = Nat.card (pCoreOf 2 H) * 72 := by
      have := hcard1
      rw [hQeq, ← hidx, hcardH, hk] at this
      calc Nat.card (pCoreOf 2 H) * (18 * k * n * m)
          = Nat.card (pCoreOf 2 H) * (18 * k) * n * m := by ring
        _ = Nat.card (pCoreOf 2 H) * Nat.card ↥(P.C.act S.G1 hG1N hG1z).range * m := by
          rw [this]
        _ = Nat.card (pCoreOf 2 H) * 72 := by rw [hm]; ring
    have e2 : 18 * k * n * m = 72 := Nat.eq_of_mul_eq_mul_left hpos e1
    exact ⟨k * m, by nlinarith [e2]⟩
  have hn1 : n = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h4
    interval_cases n <;> omega
  have := Subgroup.index_eq_one.1 (hn.trans hn1)
  apply le_antisymm hHG1
  intro x hx
  have : (⟨x, hx⟩ : ↥S.G1) ∈ H.subgroupOf S.G1 := this ▸ Subgroup.mem_top _
  exact this

end Pf1515

theorem nonempty_pf1515 (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) (S : Setting G T L V)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : Nonempty (Pf1515 S H) := by
  obtain ⟨g, hg, hQ8, hS3, hUI⟩ := S.F956_data h1323 h1326 h1336 hF956 hH hna
  obtain ⟨l, hl, hlN⟩ := S.exists_L_not_normalizer_V1
  obtain ⟨-, -, -, -, -, hUQ8⟩ := S.G248_data h1323 hG248 hH hn hna hl hlN
  obtain ⟨C⟩ := nonempty_q8Coords hUQ8
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_of_three c3p_props.1 c3p_props.2.1 c3p_props.2.2
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 (S.not_V_le_QH h1323 hH hna)
  have hzU : S.z ∈ conjClosure S.V3 H := le_conjClosure _ _ S.z_mem_V3
  have hUH : conjClosure S.V3 H ≤ H :=
    (S.hypF91 h1323 hH).conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hCz : C.z = S.z := by
    have := C.center ⟨S.z, hzU⟩ fun u => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hH.2.1 (hUH u.2))).symm
    rcases this with h | h
    · exact absurd h S.z_ne_one
    · exact h.symm
  exact ⟨⟨h1323, hG248, hC113, hH, hn, hna, g, hg, hQ8, hS3, hUI, C, hCz, c, hcL, hc, v, hv,
    hvQ⟩⟩

theorem data13515 (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) (S : Setting G T L V)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : ∃ I : Subgroup G, Data13515 S H I := by
  obtain ⟨P⟩ := nonempty_pf1515 h1323 h1326 h1336 hF956 hG248 hC113 S hH hn hna
  refine ⟨V ⊔ conjSub P.g⁻¹ V, ?_⟩
  obtain ⟨-, -, hcard, hS3⟩ := P.Idata
  exact
    { H_eq := P.H_eq_G1
      M_eq := P.normalizer_L
      V_eq := P.pCoreOf_LT
      center_QH := P.center_Q
      I_le := P.I_le_H
      I_normal := P.I_normal
      I_S3 := hS3
      card_O2_I := hcard
      H_eq_gen := P.H_eq_gen }

end Setting

theorem input13515_of (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    (hF956 : StmtF956i) (hG248 : StmtG248) (hC113 : StmtC113c) : Input13515 :=
  fun _ _ _ _ _ _ S _ hH hn hna => S.data13515 h1323 h1326 h1336 hF956 hG248 hC113 hH hn hna

end CFSG.Quasithin.H13.A5
