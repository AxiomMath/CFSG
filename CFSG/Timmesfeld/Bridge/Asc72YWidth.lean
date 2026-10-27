module

public import CFSG.Timmesfeld.Bridge.Asc72YConj
public import CFSG.Timmesfeld.Bridge.Asc72YRank

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_localGroup_of_mem (hN : IsNormalSet D) {z k x : G}
    (hx : x ∈ localGroup D (k * z * k⁻¹)) : k⁻¹ * x * k ∈ localGroup D z := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    apply mem_localGroup_of_mem
    refine ⟨by simpa using hN k⁻¹ y hy.1, ?_⟩
    have h := (Commute.conj_iff k⁻¹).mpr hy.2
    simpa [mul_assoc] using h
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show k⁻¹ * x⁻¹ * k = (k⁻¹ * x * k)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

variable [Finite G]

theorem sylow_data (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hZ : Subgroup.center G = ⊥) (hnsq : ¬ MeetsSq D) {u w v : G} (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
      (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n)
    (S₀ : Sylow 2 G) (huS : u ∈ S₀) (hvS : v ∈ S₀) (hdS : u * v * (u * v * w) ^ n ∈ S₀) :
    (D ∩ (S₀ : Set G)).ncard = 3 ∧ (∀ s ∈ S₀, Commute s ((u * v * w) ^ n)) ∧
      ∃ a ∈ S₀, a ≠ (u * v * w) ^ n ∧ IsConj ((u * v * w) ^ n) a ∧ a * a = 1 ∧
        (∀ d ∈ D ∩ (S₀ : Set G), a * d * a⁻¹ ∈ D ∩ (S₀ : Set G)) ∧
        ¬ ∃ d ∈ D ∩ (S₀ : Set G), ∃ e ∈ D ∩ (S₀ : Set G), d ≠ e ∧ Commute a d ∧
          Commute a e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  have hN := hS.normal
  have hcases := fun {t : G} (h1 : t ∈ localGroup D ((u * v * w) ^ n)) (h2 : t * t = 1) =>
    localGroup_involution_cases hS htri hn hord huw hO2 h1 h2
  have hconj := fun {g : G}
    (hg : g * (u * v * w) ^ n * g⁻¹ ∈ localGroup D ((u * v * w) ^ n)) =>
    conj_eq_of_mem_localGroup hS htri hn hord huw hO2 hg
  obtain ⟨hzz, hz1, hzu, hzv, hzw, hdD⟩ := htri.third_kind hD hN hn hord
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  have huv2 := IsTriangle.uv_mul_self hD htri
  obtain ⟨z, hzdef⟩ : ∃ z, (u * v * w) ^ n = z := ⟨_, rfl⟩
  rw [hzdef] at hcases hconj hzz hz1 hzu hzv hzw hdD hzD hdS ⊢
  have hu₀ : u ∈ D ∩ (S₀ : Set G) := ⟨htri.1, huS⟩
  have hv₀ : v ∈ D ∩ (S₀ : Set G) := ⟨htri.2.1, hvS⟩
  have hd₀ : u * v * z ∈ D ∩ (S₀ : Set G) := ⟨hdD, hdS⟩
  have hLcomm : ∀ s ∈ D ∩ (S₀ : Set G), ∀ t ∈ D ∩ (S₀ : Set G), Commute s t :=
    fun s hs t ht => hD.commute_of_isPGroup S₀.isPGroup' hs.1 ht.1 hs.2 ht.2
  have hzuvd : z = u * v * (u * v * z) := by rw [← mul_assoc, huv2, one_mul]
  have hLz : ∀ s ∈ D ∩ (S₀ : Set G), Commute s z := fun s hs => by
    rw [hzuvd]
    exact ((hLcomm s hs u hu₀).mul_right (hLcomm s hs v hv₀)).mul_right (hLcomm s hs _ hd₀)
  have hLC : ∀ s ∈ D ∩ (S₀ : Set G), s ∈ centSet D z := fun s hs => ⟨hs.1, hLz s hs⟩
  have hzS : z ∈ S₀ := by
    rw [hzuvd]
    exact S₀.mul_mem (S₀.mul_mem huS hvS) hdS
  have hnot2 : ∀ r ∈ D, ∀ s ∈ D, r ≠ s → Commute r s → z ≠ r * s :=
    fun r hr s hs hrs hc heq =>
      false_of_eq_mul_of_not_reach hS htri.1 htri.2.2.1 hzu.symm hzw.symm huw hr hs hrs hc heq
  have hmul : ∀ d ∈ D ∩ (S₀ : Set G), ∀ e ∈ D ∩ (S₀ : Set G), d ≠ e →
      d * e * z ∈ D ∩ (S₀ : Set G) := by
    intro d hd e he hde
    have hc := hLcomm d hd e he
    have hdeH : d * e ∈ localGroup D z := Subgroup.mul_mem _
      (mem_localGroup_of_mem (hLC d hd)) (mem_localGroup_of_mem (hLC e he))
    have hdee : d * e * (d * e) = 1 := by
      rw [show d * e * (d * e) = d * (e * d) * e by group, ← hc.eq,
        show d * (d * e) * e = (d * d) * (e * e) by group, hD.mul_self_eq_one hd.1,
        hD.mul_self_eq_one he.1, one_mul]
    rcases hcases hdeH hdee with h | h | h | h
    · exact absurd (hD.eq_of_mul_eq_one hd.1 h) hde
    · exact absurd h.symm (hnot2 d hd.1 e he.1 hde hc)
    · exact absurd h.1 (fun hm => hnsq ⟨d, hd.1, e, he.1, hde, hc, hm⟩)
    · exact ⟨h.1, S₀.mul_mem (S₀.mul_mem hd.2 he.2) hzS⟩
  have hzc : ∀ s ∈ S₀, Commute s z := by
    intro s hs
    have hcL : ∀ t ∈ D ∩ (S₀ : Set G), s * t * s⁻¹ ∈ localGroup D z := fun t ht =>
      mem_localGroup_of_mem (hLC _ ⟨hN s t ht.1, S₀.mul_mem (S₀.mul_mem hs ht.2) (S₀.inv_mem hs)⟩)
    have hmem : s * z * s⁻¹ ∈ localGroup D z := by
      have e1 : s * z * s⁻¹ = (s * u * s⁻¹) * (s * v * s⁻¹) * (s * (u * v * z) * s⁻¹) := by
        calc s * z * s⁻¹ = s * (u * v * (u * v * z)) * s⁻¹ := by rw [← hzuvd]
          _ = _ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hcL u hu₀) (hcL v hv₀)) (hcL _ hd₀)
    have h := hconj hmem
    show s * z = z * s
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h]
  have hnoniso : ∃ g : G, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨N, hNn, hNodd, hNz⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz fun g hg => hcon g hg
    have hN1 : N = ⊥ := hrad N hNn (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd)
    have hzc' : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hNz g
      rw [hN1, Subgroup.mem_bot, mul_inv_eq_one] at h
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
    rw [hZ] at hzc'
    exact hz1 hzc'
  obtain ⟨g, hgc, hgne⟩ := hnoniso
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hS₀C : (S₀ : Subgroup G) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs).eq
  have hbC : g * z * g⁻¹ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hgc.eq
  have hbb : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz, mul_one,
      mul_inv_cancel]
  let P : Sylow 2 C := S₀.subtype hS₀C
  have hbP : IsPGroup 2 (Subgroup.zpowers (⟨g * z * g⁻¹, hbC⟩ : C)) := by
    rintro ⟨y, hy⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hyy : y * y = 1 := by
      rcases (mem_zpowers_of_mul_self (Subtype.ext hbb : (⟨g * z * g⁻¹, hbC⟩ : C) *
        ⟨g * z * g⁻¹, hbC⟩ = 1)).mp hy with rfl | rfl
      · exact one_mul 1
      · exact Subtype.ext hbb
    simp [pow_two, hyy]
  obtain ⟨R, hR⟩ := hbP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R P
  have hcb : (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ ∈ S₀ := by
    have h1 : (⟨g * z * g⁻¹, hbC⟩ : C) ∈ (R : Subgroup C) := hR (Subgroup.mem_zpowers _)
    have h2 : c * ⟨g * z * g⁻¹, hbC⟩ * c⁻¹ ∈ ((c • R : Sylow 2 C) : Subgroup C) := by
      rw [mem_conj_sylow_iff, show c⁻¹ * (c * ⟨g * z * g⁻¹, hbC⟩ * c⁻¹) * c =
        ⟨g * z * g⁻¹, hbC⟩ by group]
      exact h1
    rw [hc] at h2
    exact h2
  obtain ⟨a, hadef⟩ : ∃ a, (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ = a := ⟨_, rfl⟩
  rw [hadef] at hcb
  have hcz : Commute (c : G) z := Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hane : a ≠ z := by
    intro h
    apply hgne
    rw [← hadef] at h
    calc g * z * g⁻¹ = (c : G)⁻¹ * ((c : G) * (g * z * g⁻¹) * (c : G)⁻¹) * c := by group
      _ = z := by rw [h, hcz.inv_left.eq, inv_mul_cancel_right]
  have haconj : IsConj z a := isConj_iff.mpr ⟨(c : G) * g, by rw [← hadef]; group⟩
  have haa : a * a = 1 := by
    rw [← hadef, show (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ * ((c : G) * (g * z * g⁻¹) * (c : G)⁻¹)
      = (c : G) * (g * z * g⁻¹ * (g * z * g⁻¹)) * (c : G)⁻¹ by group, hbb, mul_one, mul_inv_cancel]
  have haz : Commute a z := hzc a hcb
  have haL : ∀ d ∈ D ∩ (S₀ : Set G), a * d * a⁻¹ ∈ D ∩ (S₀ : Set G) := fun d hd =>
    ⟨hN a d hd.1, S₀.mul_mem (S₀.mul_mem hcb hd.2) (S₀.inv_mem hcb)⟩
  have hfix : ¬ ∃ d ∈ D ∩ (S₀ : Set G), ∃ e ∈ D ∩ (S₀ : Set G), d ≠ e ∧ Commute a d ∧
      Commute a e := by
    rintro ⟨d, hd, e, he, hde, had, hae⟩
    have hf := hmul d hd e he hde
    have haf : Commute a (d * e * z) := (had.mul_right hae).mul_right haz
    have hdd := hD.mul_self_eq_one hd.1
    have hee := hD.mul_self_eq_one he.1
    have hc' := hLcomm d hd e he
    have h1 : z = d * e * (d * e * z) := by
      calc z = (d * d) * (e * e) * z := by rw [hdd, hee, one_mul, one_mul]
        _ = d * (d * e) * e * z := by group
        _ = d * (e * d) * e * z := by rw [hc'.eq]
        _ = d * e * (d * e * z) := by group
    have hzloc : z ∈ localGroup D a := by
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_localGroup_of_mem ⟨hd.1, had.symm⟩)
        (mem_localGroup_of_mem ⟨he.1, hae.symm⟩)) (mem_localGroup_of_mem ⟨hf.1, haf.symm⟩)
    obtain ⟨k, hk⟩ := isConj_iff.mp haconj
    rw [← hk] at hzloc
    have h2 := hconj (g := k⁻¹) (by simpa using conj_mem_localGroup_of_mem hN hzloc)
    apply hane
    rw [← hk]
    calc k * z * k⁻¹ = k * (k⁻¹ * z * k⁻¹⁻¹) * k⁻¹ := by rw [h2]
      _ = z := by group
  refine ⟨?_, hzc, a, hcb, hane, haconj, haa, haL, hfix⟩
  apply le_antisymm
  · by_contra h4
    push Not at h4
    exact hfix (YRank.exists_two_commute _ hzz (fun d hd => hD.mul_self_eq_one hd.1) hLz hLcomm
      hmul (fun h => hzD h.1) haa haz haL (by omega))
  · have hdu : u * v * z ≠ u := by
      intro h
      apply hzD
      have h1 : v * z = 1 := by
        calc v * z = u⁻¹ * (u * v * z) := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      rw [show z = v⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq htri.2.1]
      exact htri.2.1
    have hdv : u * v * z ≠ v := by
      intro h
      apply hzD
      have h1 : u * z = 1 := by
        have e : u * v * z = u * z * v := by rw [mul_assoc u v z, ← hzv.eq, ← mul_assoc]
        rw [e] at h
        calc u * z = u * z * v * v⁻¹ := by group
          _ = 1 := by rw [h, mul_inv_cancel]
      rw [show z = u⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq htri.1]
      exact htri.1
    exact (Set.two_lt_ncard_iff (Set.toFinite _)).mpr ⟨u, v, u * v * z, hu₀, hv₀, hd₀,
      htri.2.2.2.1, hdu.symm, hdv.symm⟩

theorem ncard_inter_sylow_eq_three (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hZ : Subgroup.center G = ⊥) (hnsq : ¬ MeetsSq D) {u w v : G} (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
      (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n)
    (S₀ : Sylow 2 G) (huS : u ∈ S₀) (hvS : v ∈ S₀) (hdS : u * v * (u * v * w) ^ n ∈ S₀) :
    (D ∩ (S₀ : Set G)).ncard = 3 :=
  (sylow_data hS hrad hZ hnsq htri hn hord huw hO2 S₀ huS hvS hdS).1

end CFSG.Timmesfeld.Bridge.Asc72
