module

public import CFSG.Quasithin.Background.Harris.R1.D4VertModel
public import CFSG.Quasithin.Background.Harris.R1.D4VertPres
public import CFSG.Quasithin.Background.Harris.R1.D4Iso
public import CFSG.Quasithin.Background.Harris.R1.D4Klein
public import CFSG.Quasithin.Background.Harris.R1.D4ModelV
public import CFSG.Quasithin.Background.Harris.R1.D4SetL2B
public import CFSG.Quasithin.Background.Harris.R1.J2VertSym
public import CFSG.Quasithin.Background.Harris.R1.Q8L2BFacts

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.D4Hex
  CFSG.LargeExtraspecial.S63 CFSG.CosetTable CFSG.LieType.BorelTits

structure D4HFacts :
    Prop where
  z_eq : d4Word (hWords.getD 0 []) = d4z
  x_eq : d4Word (hWords.getD 1 []) = vB
  a_mem : d4Word (hWords.getD 2 []) ∈ d4H
  b_mem : d4Word (hWords.getD 3 []) ∈ d4H
  card_H : Nat.card d4H = 258048
  card_U : Nat.card d4U = 4096
  card_B : Nat.card d4B = 28672
  U_le_B : d4U ≤ d4B
  normalizer_U : Subgroup.normalizer (d4U : Set D) = d4B


section Iso

variable {G : Type} [Group G]

theorem subtype_evalWord {K : Subgroup G} {m : ℕ} (g : Fin m → ↥K) (r : List (Fin m × Bool)) :
    ((evalWord g r : ↥K) : G) = evalWord (fun i => (g i : G)) r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    rw [evalWord_cons, evalWord_cons, Subgroup.coe_mul, ih]
    split_ifs <;> simp

theorem exists_pg_equiv {K : Subgroup G} (g : Fin 4 → G)
    (hg : ∀ i, g i ∈ K) (hrel : ∀ r ∈ hRels, evalWord g r = 1)
    (hcl : Subgroup.closure (Set.range g) = K) (hK : Nat.card K = 258048) :
    ∃ p : PG 4 hRels ≃* ↥K, ∀ i, (p (PresentedGroup.of i) : G) = g i := by
  set gK : Fin 4 → ↥K := fun i => ⟨g i, hg i⟩ with hgK
  have hp : ∀ r ∈ hRels, (r.map fun p => if p.2 then gK p.1 else (gK p.1)⁻¹).prod = 1 := by
    intro r hr
    apply Subtype.ext
    have := subtype_evalWord gK r
    rw [show (fun i => ((gK i : ↥K) : G)) = g from rfl] at this
    exact this.trans (hrel r hr)
  have hsurj : Function.Surjective (J2Vert.pgHom hp) := by
    rw [← MonoidHom.range_eq_top, J2Vert.range_pgHom]
    subst hcl
    have h := Subgroup.closure_closure_coe_preimage (k := Set.range g)
    convert h using 2
    ext y
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩
  obtain ⟨hfin, hle⟩ := card_PG_h_le
  have hbij : Function.Bijective (J2Vert.pgHom hp) :=
    hsurj.bijective_of_nat_card_le (by rw [hK]; exact hle)
  exact ⟨MulEquiv.ofBijective _ hbij, fun i => by
    show ((J2Vert.pgHom hp (PresentedGroup.of i) : ↥K) : G) = g i
    rw [J2Vert.pgHom_of]⟩

end Iso


section V1

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G]
  in
theorem charTwo_K1 [Finite G] (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S)
    (hSK : S ≤ K1) : CharTwo K1 := by
  have h := hR.hyp.h1.charTwo
  have he : K1 ⊔ S ⊔ borelOf L2 S = K1 :=
    le_antisymm (sup_le (sup_le le_rfl hSK) ((F112J2.borelOf_L2_le_S hset hR).trans hSK))
      (le_sup_left.trans le_sup_left)
  rwa [he] at h

theorem exists_v1_iso (hH : D4HFacts) (hset : R1SettingLegacyBare K1 L2 S Zs) (hR : Hyp111R K1 L2 S)
    (hSK : S ≤ K1) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hK : Nat.card K1 = 258048) {z x a b : G} (hz : z ∈ Zs) (hz1 : z ≠ 1)
    (hxV : x ∈ conjClosure Zs L2) (hxZ : x ∉ Zs) (haK : a ∈ K1) (hbK : b ∈ K1)
    (hrel : ∀ r ∈ hRels, evalWord ![z, x, a, b] r = 1)
    (hcl : Subgroup.closure ({z, x, a, b} : Set G) = K1) :
    ∃ e : ↥K1 ≃* ↥d4H, (∀ k : ↥K1, (k : G) ∈ S ↔ (e k : D) ∈ d4U) ∧
      (∀ k : ↥K1, (k : G) ∈ conjClosure Zs L2 ↔ (e k : D) ∈ d4V) ∧
      (∀ k : ↥K1, (k : G) ∈ bigB K1 L2 S ↔ (e k : D) ∈ d4B) := by
  classical
  set V := conjClosure Zs L2 with hVdef
  have hWK : vBeta K1 L2 S Zs ≤ K1 := hQK ▸ pCoreOf_le 2 K1
  have hVW : V ≤ vBeta K1 L2 S Zs := le_conjClosure V (K1 ⊔ S)
  have hVK : V ≤ K1 := hVW.trans hWK
  have hZV : Zs ≤ V := le_conjClosure Zs L2
  have hzK : z ∈ K1 := hVK (hZV hz)
  have hxK : x ∈ K1 := hVK hxV
  set g : Fin 4 → G := ![z, x, a, b] with hgdef
  have hgK : ∀ i, g i ∈ K1 := by
    intro i; fin_cases i
    exacts [hzK, hxK, haK, hbK]
  have hrange : Set.range g = ({z, x, a, b} : Set G) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [hgdef]
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  obtain ⟨p, hp⟩ := exists_pg_equiv g hgK hrel (by rw [hrange, hcl]) hK
  set ψ : ↥K1 →* D := hModel.comp p.symm.toMonoidHom with hψdef
  have hψg : ∀ i, ψ ⟨g i, hgK i⟩ = d4Word (hWords.getD i.val []) := by
    intro i
    have : (⟨g i, hgK i⟩ : ↥K1) = p (PresentedGroup.of i) := Subtype.ext (hp i).symm
    rw [hψdef, MonoidHom.comp_apply, this]
    show hModel (p.symm (p (PresentedGroup.of i))) = _
    rw [MulEquiv.symm_apply_apply, hModel_of]
  have hψz : ψ ⟨z, hzK⟩ = d4z := (hψg 0).trans hH.z_eq
  have hψx : ψ ⟨x, hxK⟩ = vB := (hψg 1).trans hH.x_eq
  set P : Subgroup ↥K1 := (pCoreOf 2 K1).subgroupOf K1 with hPdef
  have hPn : P.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 K1)).mpr
      (le_normalizer_pCoreOf 2 K1)
  have hP2 : IsPGroup 2 P :=
    (pCoreOf_isPGroup 2 K1).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 K1)).symm
  have hchar := charTwo_K1 hset hR hSK
  have hPC : Subgroup.centralizer (P : Set ↥K1) ≤ P := by
    intro k hk
    have hk' : (k : G) ∈ K1 ⊓ Subgroup.centralizer (pCoreOf 2 K1 : Set G) := by
      refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hk ⟨q, pCoreOf_le 2 K1 hq⟩
        (Subgroup.mem_subgroupOf.mpr hq)
      exact congrArg Subtype.val this
    exact Subgroup.mem_subgroupOf.mpr (hchar hk')
  have hZP : ∀ y ∈ P, (∀ w ∈ P, y * w = w * y) → y = 1 ∨ y = ⟨z, hzK⟩ := by
    intro y hy hyc
    have hyW : (y : G) ∈ vBeta K1 L2 S Zs := hQK ▸ Subgroup.mem_subgroupOf.mp hy
    have hyZ : (y : G) ∈ Zs := hcen _ hyW fun u hu => by
      have hu' : u ∈ K1 := hWK hu
      have := hyc ⟨u, hu'⟩ (Subgroup.mem_subgroupOf.mpr (hQK ▸ hu))
      exact congrArg Subtype.val this
    rcases J2Vert.mem_Zs_cases hset hz hz1 hyZ with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hψinj : Function.Injective ψ :=
    injective_of_center_le hP2 hPC hZP ψ (by rw [hψz]; exact d4z_sq.2)
  have hzH : d4z ∈ d4H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hVH : ∀ v ∈ d4V, v ∈ d4H := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (d4V_comm v hv d4z (mem_d4V_iff.mpr
      (Or.inr (Or.inl rfl))))
  have himg : ∀ i : Fin 4, d4Word (hWords.getD i.val []) ∈ d4H := by
    intro i
    fin_cases i
    · show d4Word (hWords.getD 0 []) ∈ d4H
      rw [hH.z_eq]; exact hzH
    · show d4Word (hWords.getD 1 []) ∈ d4H
      rw [hH.x_eq]; exact hVH _ (mem_d4V_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hH.a_mem
    · exact hH.b_mem
  have hmodH : hModel.range ≤ d4H := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hModel_of]
    exact himg i
  have hψH : ∀ k, ψ k ∈ d4H := fun k => hmodH ⟨p.symm k, rfl⟩
  have hψrange : ψ.range = d4H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨k, rfl⟩; exact hψH k
    · rw [hH.card_H, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, hK]
  set e : ↥K1 ≃* ↥d4H := (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)
    with hedef
  have he : ∀ k, (e k : D) = ψ k := fun k => rfl
  have hpre : ∀ d ∈ d4H, ∃ k : ↥K1, ψ k = d := fun d hd => by
    rw [← hψrange] at hd
    obtain ⟨k, hk⟩ := hd
    exact ⟨k, hk⟩
  have hVea := SzR1.MNU.V_elemAbelian_of_setting hset hR
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hVea.2 v hv
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Zs.one_mem)
  have hzx : z ≠ x := fun h => hxZ (h ▸ hz)
  have hVcases : ∀ c ∈ V, c = 1 ∨ c = z ∨ c = x ∨ c = z * x :=
    fun c hc => klein_mem_cases hset.V_card hV2 (hZV hz) hxV hz1 hx1 hzx hc
  have hψzx : ψ (⟨z, hzK⟩ * ⟨x, hxK⟩) = vC := by
    rw [map_mul, hψz, hψx]; exact d4V_rels.1
  have heV : ∀ k : ↥K1, (k : G) ∈ V ↔ (e k : D) ∈ d4V := by
    intro k
    rw [he]
    constructor
    · intro hk
      rcases hVcases _ hk with h | h | h | h
      · rw [show k = 1 from Subtype.ext h, map_one]; exact d4V.one_mem
      · rw [show k = ⟨z, hzK⟩ from Subtype.ext h, hψz]
        exact mem_d4V_iff.mpr (Or.inr (Or.inl rfl))
      · rw [show k = ⟨x, hxK⟩ from Subtype.ext h, hψx]
        exact mem_d4V_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [show k = ⟨z, hzK⟩ * ⟨x, hxK⟩ from Subtype.ext h, hψzx]
        exact mem_d4V_iff.mpr (Or.inr (Or.inr (Or.inr rfl)))
    · intro hk
      rcases mem_d4V_iff.mp hk with h | h | h | h
      · rw [hψinj (h.trans (map_one ψ).symm)]; exact V.one_mem
      · rw [hψinj (h.trans hψz.symm)]; exact hZV hz
      · rw [hψinj (h.trans hψx.symm)]; exact hxV
      · rw [hψinj (h.trans hψzx.symm)]; exact V.mul_mem (hZV hz) hxV
  have hSV : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V := fun s hs v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (F112J2.bigB_le_normalizer_V hset hR ((le_sup_right : S ≤ bigB K1 L2 S) hs)) v).mp hv
  set T : Subgroup D := (S.subgroupOf K1).map ψ with hTdef
  have hTB : T ≤ d4B := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hψH s, mem_d4N_of_normalizes fun v' hv' => ?_⟩
    obtain ⟨k, rfl⟩ := hpre v' (hVH v' hv')
    have hkV : (k : G) ∈ V := (heV k).mpr hv'
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (heV _).mp (hSV _ (Subgroup.mem_subgroupOf.mp hs) _ hkV)
  have hScard : Nat.card S = 2 ^ 12 := card_S_of_sylow hR.hyp.h1.sylow hSK hK
  have hTcard : Nat.card T = 4096 := by
    rw [hTdef, Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hScard]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 12) (by rw [hTcard]; norm_num)
  have hU2 : IsPGroup 2 d4U := IsPGroup.of_card (n := 12) (by rw [hH.card_U]; norm_num)
  have hTU : T = d4U := by
    have hsup2 : IsPGroup 2 (T ⊔ d4U : Subgroup D) :=
      IsPGroup.to_sup_of_normal_right' hT2 hU2 (hTB.trans hH.normalizer_U.symm.le)
    have hsupB : T ⊔ d4U ≤ d4B := sup_le hTB hH.U_le_B
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hsup2
    have hdvd := Subgroup.card_dvd_of_le hsupB
    rw [hn, hH.card_B, show (28672 : ℕ) = 2 ^ 12 * 7 by norm_num] at hdvd
    have hdvd' : 2 ^ n ∣ 2 ^ 12 :=
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 7)).dvd_of_dvd_mul_right hdvd
    have hle : Nat.card (T ⊔ d4U : Subgroup D) ≤ Nat.card d4U := by
      rw [hn, hH.card_U, show (4096 : ℕ) = 2 ^ 12 by norm_num]
      exact Nat.le_of_dvd (by positivity) hdvd'
    have heq : d4U = T ⊔ d4U := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    have hTle : T ≤ d4U := heq ▸ le_sup_left
    exact Subgroup.eq_of_le_of_card_ge hTle (by rw [hTcard, hH.card_U])
  have heS : ∀ k : ↥K1, (k : G) ∈ S ↔ (e k : D) ∈ d4U := by
    intro k
    rw [he, ← hTU]
    constructor
    · intro hk; exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    · rintro ⟨s, hs, hsk⟩
      rw [← hψinj hsk]
      exact Subgroup.mem_subgroupOf.mp hs
  have heB : ∀ k : ↥K1, (k : G) ∈ bigB K1 L2 S ↔ (e k : D) ∈ d4B := by
    intro k
    rw [bigB_eq_of_le hset hR hSK, Subgroup.mem_inf, ← hH.normalizer_U, he,
      Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    simp only [k.2, true_and]
    constructor
    · intro hk d
      constructor
      · intro hd
        obtain ⟨s, rfl⟩ := hpre d (hH.U_le_B.trans inf_le_left hd)
        have hs : (s : G) ∈ S := (heS s).mpr hd
        rw [← map_inv, ← map_mul, ← map_mul]
        exact (heS _).mp ((hk s).mp hs)
      · intro hd
        have hdH : d ∈ d4H := by
          have h1 : ψ k * d * (ψ k)⁻¹ ∈ d4H := hH.U_le_B.trans inf_le_left hd
          have : d = (ψ k)⁻¹ * (ψ k * d * (ψ k)⁻¹) * ψ k := by group
          rw [this]
          exact d4H.mul_mem (d4H.mul_mem (d4H.inv_mem (hψH k)) h1) (hψH k)
        obtain ⟨s, rfl⟩ := hpre d hdH
        rw [← map_inv, ← map_mul, ← map_mul] at hd
        exact (heS s).mp ((hk s).mpr ((heS _).mpr hd))
    · intro hU g
      by_cases hg : g ∈ K1
      · have h1 := heS ⟨g, hg⟩
        have h2 := heS (k * ⟨g, hg⟩ * k⁻¹)
        rw [he] at h1 h2
        rw [map_mul, map_mul, map_inv] at h2
        exact h1.trans ((hU _).trans h2.symm)
      · constructor
        · intro h; exact absurd (hSK h) hg
        · intro h
          exfalso
          apply hg
          have : g = (k : G)⁻¹ * ((k : G) * g * (k : G)⁻¹) * k := by group
          rw [this]
          exact K1.mul_mem (K1.mul_mem (K1.inv_mem k.2) (hSK h)) k.2
  exact ⟨e, heS, heV, heB⟩

end V1

end CFSG.Quasithin.Background.Harris.R1.D4Vert
