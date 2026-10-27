module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eStab
public import CFSG.Milestones.ASVolI.F48.Rest.U52eChart
public import Certificates.Certificate7777

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr burnsideF48t_u52eF

section Conj

variable {D : Type} [Group D] {n : ℕ} {G : Fin n → D} {P1 P2 : Subgroup D} {S1 S2 : Set (Fin n)}
  {K : Subgroup D} {R1 R2 XW YW KW : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48t_conj_props {K'' : Subgroup D} {t : D} (ht : t ∈ P1 ⊓ P2)
    (hiff : ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K) {x : D} (hx : x ∈ P1) (hx2 : x ∉ P2)
    (hxK : ∀ k ∈ K'', x * k * x⁻¹ ∈ K'') (hxx : x * x ∈ K'') :
    t * x * t⁻¹ ∈ P1 ∧ t * x * t⁻¹ ∉ P2 ∧
      (∀ k ∈ K, (t * x * t⁻¹) * k * (t * x * t⁻¹)⁻¹ ∈ K) ∧ (t * x * t⁻¹) * (t * x * t⁻¹) ∈ K := by
  refine ⟨P1.mul_mem (P1.mul_mem ht.1 hx) (P1.inv_mem ht.1), fun h => hx2 ?_, fun k hk => ?_, ?_⟩
  · have := P2.mul_mem (P2.mul_mem (P2.inv_mem ht.2) h) ht.2
    simpa [mul_assoc] using this
  · have h1 : t⁻¹ * k * t ∈ K'' := (hiff _).2 (by simpa [mul_assoc] using hk)
    have h2 := (hiff _).1 (hxK _ h1)
    have e : t * (x * (t⁻¹ * k * t) * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * k * (t * x * t⁻¹)⁻¹ := by group
    rwa [e] at h2
  · have e : t * (x * x) * t⁻¹ = (t * x * t⁻¹) * (t * x * t⁻¹) := by group
    rw [← e]
    exact (hiff _).1 hxx

theorem burnsideF48t_core_conj [Finite D]
    (hF : burnsideF48t_Facts G P1 P2 S1 S2 K R1 R2 XW YW KW m)
    {Y : Type} [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)
    (h12 : ∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hinj : Function.Injective f₁)
    (hcard : Nat.card D ≤ Nat.card Y) {K'' : Subgroup D} (hK''le : K'' ≤ P1 ⊓ P2) {t : D}
    (ht : t ∈ P1 ⊓ P2) (hiff : ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K) {x y : D} (hx : x ∈ P1)
    (hy : y ∈ P2) (hx2 : x ∉ P2) (hxK : ∀ k ∈ K'', x * k * x⁻¹ ∈ K'') (hxx : x * x ∈ K'')
    (hy1 : y ∉ P1) (hyK : ∀ k ∈ K'', y * k * y⁻¹ ∈ K'') (hyy : y * y ∈ K'')
    (hrel : ∀ k₁ (hk₁ : k₁ ∈ K'') k₂ (hk₂ : k₂ ∈ K''), ∃ c, ∃ hc : c ∈ K'',
      (f₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ *
        f₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩) :
    ∃ φ : Y ≃* D, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z := by
  obtain ⟨hx', hx2', hxK', hxx'⟩ := burnsideF48t_conj_props ht hiff hx hx2 hxK hxx
  obtain ⟨hy', hy1', hyK', hyy'⟩ := burnsideF48t_conj_props (P1 := P2) (P2 := P1) ⟨ht.2, ht.1⟩
    hiff hy hy1 hyK hyy
  have hkK'' : ∀ {k : D}, k ∈ K → t⁻¹ * k * t ∈ K'' := fun hk =>
    (hiff _).2 (by simpa [mul_assoc] using hk)
  have hrel' : ∀ k₁ (hk₁ : k₁ ∈ K) k₂ (hk₂ : k₂ ∈ K), ∃ c, ∃ hc : c ∈ K,
      (f₁ ⟨t * x * t⁻¹ * k₁, P1.mul_mem hx' (hF.K_le hk₁).1⟩ *
        f₂ ⟨t * y * t⁻¹ * k₂, P2.mul_mem hy' (hF.K_le hk₂).2⟩) ^ m =
          f₁ ⟨c, (hF.K_le hc).1⟩ := by
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨c, hc, hrc⟩ := hrel _ (hkK'' hk₁) _ (hkK'' hk₂)
    have hcK : t * c * t⁻¹ ∈ K := (hiff _).1 hc
    refine ⟨t * c * t⁻¹, hcK, ?_⟩
    have e1 : (⟨t * x * t⁻¹ * k₁, P1.mul_mem hx' (hF.K_le hk₁).1⟩ : ↥P1) =
        ⟨t, ht.1⟩ * ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          (⟨t, ht.1⟩ : ↥P1)⁻¹ := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e2 : (⟨t * y * t⁻¹ * k₂, P2.mul_mem hy' (hF.K_le hk₂).2⟩ : ↥P2) =
        ⟨t, ht.2⟩ * ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩ *
          (⟨t, ht.2⟩ : ↥P2)⁻¹ := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e3 : (⟨t * c * t⁻¹, (hF.K_le hcK).1⟩ : ↥P1) =
        ⟨t, ht.1⟩ * ⟨c, (hK''le hc).1⟩ * (⟨t, ht.1⟩ : ↥P1)⁻¹ := rfl
    rw [e1, e2, e3, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, map_mul,
      map_inv, ← h12 t ht]
    have e : f₁ ⟨t, ht.1⟩ * f₁ ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          (f₁ ⟨t, ht.1⟩)⁻¹ *
        (f₁ ⟨t, ht.1⟩ * f₂ ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩ *
          (f₁ ⟨t, ht.1⟩)⁻¹) =
        f₁ ⟨t, ht.1⟩ * (f₁ ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          f₂ ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩) *
          (f₁ ⟨t, ht.1⟩)⁻¹ := by
      group
    rw [e, conj_pow, hrc]
  exact burnsideF48t_core hF f₁ f₂ h12 hgen hinj hcard hx' hx2' hxK' hxx' hy' hy1' hyK' hyy' hrel'

end Conj

@[expose] noncomputable def burnsideF48t_u52eKh (j : ℕ) : Subgroup ↥burnsideF48t_u52Xh :=
  (burnsideF48t_u52eK' j).subgroupOf burnsideF48t_u52Xh

@[expose] noncomputable def burnsideF48t_u52eK0 : Subgroup ↥burnsideF48t_u52Xh :=
  burnsideF48t_u52K'.subgroupOf burnsideF48t_u52Xh

@[expose] noncomputable def burnsideF48t_u52eB : Subgroup ↥burnsideF48t_u52Xh :=
  burnsideF48t_u52B'.subgroupOf burnsideF48t_u52Xh

@[expose] def burnsideF48t_u52eQ (K'' : Subgroup ↥burnsideF48t_u52Xh) : Prop :=
  Nat.card ↥K'' = 18 ∧ ∀ z ∈ K'', (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52S0' → z = 1

section Engine


theorem burnsideF48t_u52e_rels : ∀ r ∈ burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2,
    burnsideF48s_ev (fun i : Fin 5 => burnsideF48t_u52eσ i) r = 1 := by
  have h := burnsideF48t_u52e_cert.2.2.1
  simp only [burnsideF48t_u52eRelOK] at h
  intro r hr
  exact burnsideF48t_ev_eq_one_of burnsideF48t_u52e_recL (List.all_eq_true.1 h r hr)

theorem burnsideF48t_u52e_σ_B {i : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 4) :
    burnsideF48t_u52eσ i ∈ burnsideF48t_u52Xh ⊓
      (MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB) := by
  have hi5 : i < 5 := by omega
  refine ⟨burnsideF48t_u52e_σ_mem hi5, MulAction.mem_stabilizer_iff.2 ?_,
    MulAction.mem_stabilizer_iff.2 ?_⟩
  · rw [Equiv.Perm.smul_def]
    exact burnsideF48t_u52e_σ_pA hi5 (by omega)
  · rw [Equiv.Perm.smul_def]
    exact burnsideF48t_u52e_σ_pB hi5 (by omega)

theorem burnsideF48t_u52e_K'_le_B {j : ℕ} (hj : j < 4) : burnsideF48t_u52eK' j ≤
    burnsideF48t_u52Xh ⊓ (MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB) := by
  rw [burnsideF48t_u52e_K'_eq hj, Subgroup.closure_le]
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  have hlet : ∀ ws ∈ burnsideF48t_u52eKhW, ∀ w ∈ ws, ∀ l ∈ w,
      (l.1 : ℕ) = 0 ∨ (l.1 : ℕ) = 1 ∨ (l.1 : ℕ) = 4 := by decide
  have hj4 : j < burnsideF48t_u52eKhW.length := by
    rw [show burnsideF48t_u52eKhW.length = 4 from rfl]
    exact hj
  have hws : burnsideF48t_u52eKhW.getD j [] ∈ burnsideF48t_u52eKhW := by
    rw [List.getD_eq_getElem _ _ hj4]
    exact List.getElem_mem _
  have hs3 : s < 3 := by rwa [burnsideF48t_u52e_KG_size] at hs
  have hm : burnsideF48t_u52eKGen s < 18 := by interval_cases s <;> decide
  have hlen : burnsideF48t_u52eKGen s < (burnsideF48t_u52eKhW.getD j []).length := by
    rw [burnsideF48t_u52e_KhW_length hj]
    exact hm
  have hw : (burnsideF48t_u52eKhW.getD j []).getD (burnsideF48t_u52eKGen s) [] ∈
      burnsideF48t_u52eKhW.getD j [] := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  refine burnsideF48s_ev_mem _ _ fun l hl => ?_
  exact burnsideF48t_u52e_σ_B (hlet _ hws _ hw l hl)

theorem burnsideF48t_u52e_K'_le_Xh {j : ℕ} (hj : j < 4) : burnsideF48t_u52eK' j ≤ burnsideF48t_u52Xh :=
  fun _ hz => (burnsideF48t_u52e_K'_le_B hj hz).1

theorem burnsideF48t_u52e_card_Kh {j : ℕ} (hj : j < 4) : Nat.card ↥(burnsideF48t_u52eKh j) = 18 := by
  rw [burnsideF48t_u52eKh, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (burnsideF48t_u52e_K'_le_Xh hj)).toEquiv, burnsideF48t_u52e_card_K' hj]

theorem burnsideF48t_u52e_Kh_le {j : ℕ} (hj : j < 4) :
    burnsideF48t_u52eKh j ≤ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2 := fun z hz => by
  obtain ⟨-, h1, h2⟩ := burnsideF48t_u52e_K'_le_B hj hz
  exact ⟨(burnsideF48t_u52e_mem_P1 z).2 (MulAction.mem_stabilizer_iff.1 h1),
    (burnsideF48t_u52e_mem_P2 z).2 (MulAction.mem_stabilizer_iff.1 h2)⟩

theorem burnsideF48t_u52e_B_le : burnsideF48t_u52eB ≤ burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2 :=
  fun z hz => by
    have h : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B' := hz
    rw [burnsideF48t_u52_B'_eq, burnsideF48t_u52_P1'_eq, burnsideF48t_u52_P2'_eq] at h
    exact ⟨(burnsideF48t_u52e_mem_P1 z).2 (MulAction.mem_stabilizer_iff.1 h.1.2),
      (burnsideF48t_u52e_mem_P2 z).2 (MulAction.mem_stabilizer_iff.1 h.2.2)⟩

theorem burnsideF48t_u52e_lift {j : ℕ} (hj : j < 4) {x : ↥burnsideF48t_u52Xh}
    (hxK : ∀ k ∈ burnsideF48t_u52eKh j, x * k * x⁻¹ ∈ burnsideF48t_u52eKh j)
    (hxx : x * x ∈ burnsideF48t_u52eKh j) :
    (∀ k ∈ burnsideF48t_u52eK' j,
      (x : Equiv.Perm (Fin 462)) * k * (x : Equiv.Perm (Fin 462))⁻¹ ∈ burnsideF48t_u52eK' j) ∧
    (x : Equiv.Perm (Fin 462)) * x ∈ burnsideF48t_u52eK' j := by
  have hK : ∀ k ∈ burnsideF48t_u52eK' j,
      (x : Equiv.Perm (Fin 462)) * k * (x : Equiv.Perm (Fin 462))⁻¹ ∈ burnsideF48t_u52eK' j := by
    intro k hk
    have := hxK ⟨k, burnsideF48t_u52e_K'_le_Xh hj hk⟩ hk
    rw [burnsideF48t_u52eKh, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    exact this
  have hxx' : (x : Equiv.Perm (Fin 462)) * x ∈ burnsideF48t_u52eK' j := by
    have := hxx
    rw [burnsideF48t_u52eKh, Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
    exact this
  exact ⟨hK, hxx'⟩

theorem burnsideF48t_u52e_nox {j : ℕ} (hj : j = 0 ∨ j = 1) {x : ↥burnsideF48t_u52Xh}
    (hx : x ∈ burnsideF48t_u52eP1) (hx2 : x ∉ burnsideF48t_u52eP2)
    (hxK : ∀ k ∈ burnsideF48t_u52eKh j, x * k * x⁻¹ ∈ burnsideF48t_u52eKh j)
    (hxx : x * x ∈ burnsideF48t_u52eKh j) : False := by
  have hx0 := (burnsideF48t_u52e_mem_P1 x).1 hx
  have hxB : (x : Equiv.Perm (Fin 462)) burnsideF48t_u52pB ≠ burnsideF48t_u52pB :=
    fun h => hx2 ((burnsideF48t_u52e_mem_P2 x).2 h)
  obtain ⟨hK, hxx'⟩ := burnsideF48t_u52e_lift (by omega) hxK hxx
  exact (burnsideF48t_u52e_tests1 x.2 hx0 hxB).1 j hj hK hxx'

theorem burnsideF48t_u52e_noy {y : ↥burnsideF48t_u52Xh} (hy : y ∈ burnsideF48t_u52eP2)
    (hy1 : y ∉ burnsideF48t_u52eP1)
    (hyK : ∀ k ∈ burnsideF48t_u52eKh 3, y * k * y⁻¹ ∈ burnsideF48t_u52eKh 3)
    (hyy : y * y ∈ burnsideF48t_u52eKh 3) : False := by
  have hy0 := (burnsideF48t_u52e_mem_P2 y).1 hy
  have hyA : (y : Equiv.Perm (Fin 462)) burnsideF48t_u52pA ≠ burnsideF48t_u52pA :=
    fun h => hy1 ((burnsideF48t_u52e_mem_P1 y).2 h)
  obtain ⟨hK, hyy'⟩ := burnsideF48t_u52e_lift (by norm_num) hyK hyy
  exact (burnsideF48t_u52e_tests2 y.2 hy0 hyA).2 hK hyy'

theorem burnsideF48t_u52e_restrict {i j k : ℕ} (hj : j < 2) :
    restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48t_u52eWs i j k) = burnsideF48t_u52eWsB := by
  have hy : ∀ v ∈ burnsideF48t_u52eYW, ∃ b, ((3 : Fin 5), b) ∈ v := by decide
  have hv : burnsideF48t_u52eYW.getD j [] ∈ burnsideF48t_u52eYW := by
    rw [List.getD_eq_getElem _ _ (by simpa [burnsideF48t_u52eYW] using hj)]
    exact List.getElem_mem _
  obtain ⟨b, hb⟩ := hy _ hv
  have hmem : ((3 : Fin 5), b) ∈ burnsideF48s_eCandRel 4 (burnsideF48t_u52eXW.getD i [])
      (burnsideF48t_u52eYW.getD j []) ((burnsideF48t_u52eKhW.getD 2 []).getD k []) := by
    simp only [burnsideF48s_eCandRel, List.mem_append, List.mem_flatten, List.mem_replicate]
    exact Or.inl ⟨_, ⟨by norm_num, rfl⟩, List.mem_append_right _ hb⟩
  have hn := burnsideF48t_renumber_none (S := subsetOf 5 [0, 1, 2, 4]) hmem
    (show (3 : Fin 5) ∉ subsetOf 5 [0, 1, 2, 4] by decide)
  simp only [burnsideF48t_u52eWs, burnsideF48s_eWs, restrictWords, List.filterMap_append,
    List.filterMap_cons, hn, List.filterMap_nil, List.append_nil]

theorem burnsideF48t_u52e_tc {t : ℕ × ℕ × ℕ × ℕ} (ht : t ∈ burnsideF48t_u52eCands) :
    Finite (PG 5 (burnsideF48t_u52eWs t.1 t.2.1 t.2.2.1)) ∧
      Nat.card (PG 5 (burnsideF48t_u52eWs t.1 t.2.1 t.2.2.1)) ≤ t.2.2.2 * 165888 :=
  Certificates.certificate7777 t ht

theorem burnsideF48t_u52e_cand {i j k : ℕ} (hi : i < 4) (hj : j < 2) (hk : k < 18) :
    (∃ t ∈ burnsideF48t_u52eCands, t.1 = i ∧ t.2.1 = j ∧ t.2.2.1 = k ∧
      (t.2.2.2 = 165 → burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l)
        (burnsideF48s_eCandRel 4 (burnsideF48t_u52eXW.getD i []) (burnsideF48t_u52eYW.getD j [])
          ((burnsideF48t_u52eKhW.getD 2 []).getD k [])) = 1)) ∨
    ¬ (burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) (burnsideF48t_u52eXW.getD i []) *
        burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) (burnsideF48t_u52eYW.getD j []) *
        burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) ((burnsideF48t_u52eKhW.getD 2 []).getD k []) =
      burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) ((burnsideF48t_u52eKhW.getD 2 []).getD k []) *
        (burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) (burnsideF48t_u52eXW.getD i []) *
          burnsideF48s_ev (fun l : Fin 5 => burnsideF48t_u52eσ l) (burnsideF48t_u52eYW.getD j []))) := by
  have h := burnsideF48t_u52e_cert.2.2.2.2
  simp only [burnsideF48t_u52eCandOK] at h
  have h1 := allBelowN_spec (allBelowN_spec (allBelowN_spec h hi) hj) hk
  have hrec := burnsideF48t_u52e_recL
  split at h1
  · rename_i t ht
    left
    refine ⟨t, List.mem_of_find?_eq_some ht, ?_⟩
    have hp := List.find?_some ht
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1', h2'⟩, h3'⟩ := hp
    refine ⟨h1', h2', h3', fun h165 => ?_⟩
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h165, not_true_eq_false, false_or] at h1
    exact burnsideF48t_ev_eq_one_of hrec h1
  · right
    intro he
    simp only [Bool.not_eq_true'] at h1
    have hu := burnsideF48t_prep_evA hrec (burnsideF48t_u52eXW.getD i [])
    have hv := burnsideF48t_prep_evA hrec (burnsideF48t_u52eYW.getD j [])
    have hc := burnsideF48t_prep_evA hrec ((burnsideF48t_u52eKhW.getD 2 []).getD k [])
    have := (peq_iff (prep_pcomp (prep_pcomp hu hv) hc) (prep_pcomp hc (prep_pcomp hu hv))).2 he
    rw [this] at h1
    exact absurd h1 (by decide)

theorem burnsideF48t_u52e_facts : burnsideF48t_Facts burnsideF48t_u52eL burnsideF48t_u52eP1
    burnsideF48t_u52eP2 burnsideF48t_u52eS1 burnsideF48t_u52eS2 (burnsideF48t_u52eKh 2)
    burnsideF48t_u52eR1 burnsideF48t_u52eR2 burnsideF48t_u52eXW burnsideF48t_u52eYW
    (burnsideF48t_u52eKhW.getD 2 []) 4 where
  hP1 := rfl
  hP2 := rfl
  rel1 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_u52eR1, ∀ l ∈ r, l.1 ≠ 3 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_u52e_coe_ev r).trans (burnsideF48t_u52e_rels r
      (List.mem_append_left _ hr)))⟩
  rel2 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_u52eR2, ∀ l ∈ r, l.1 ≠ 2 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_u52e_coe_ev r).trans (burnsideF48t_u52e_rels r
      (List.mem_append_right _ hr)))⟩
  sup := by
    have hle1 : burnsideF48t_u52P1.map burnsideF48t_u52eι ≤ burnsideF48t_u52eP1 := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact (burnsideF48t_u52e_mem_P1 _).2 ((burnsideF48t_u52_mem_P1_iff x).1 hx)
    have hle2 : burnsideF48t_u52P2.map burnsideF48t_u52eι ≤ burnsideF48t_u52eP2 := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      exact (burnsideF48t_u52e_mem_P2 _).2 ((burnsideF48t_u52_mem_P2_iff x).1 hx)
    have hX : ∀ w : ↥burnsideF48t_u52Xh, (w : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X →
        w ∈ burnsideF48t_u52eP1 ⊔ burnsideF48t_u52eP2 := by
      intro w hw
      have h1 : (⟨w, hw⟩ : ↥burnsideF48t_u52X) ∈ burnsideF48t_u52P1 ⊔ burnsideF48t_u52P2 := by
        rw [burnsideF48t_u52_facts.sup]
        exact Subgroup.mem_top _
      have h2 := Subgroup.mem_map_of_mem burnsideF48t_u52eι h1
      rw [Subgroup.map_sup] at h2
      exact sup_le_sup hle1 hle2 h2
    rw [eq_top_iff]
    intro z _
    rcases (burnsideF48t_u52e_mem_Xh z).1 z.2 with h | h
    · exact hX z h
    · have hfP : (⟨burnsideF48t_u52f, burnsideF48t_u52e_f_mem⟩ : ↥burnsideF48t_u52Xh) ∈
          burnsideF48t_u52eP1 :=
        Subgroup.subset_closure ⟨4, show (4 : Fin 5) ≠ 3 by decide, rfl⟩
      have h2 := hX ⟨burnsideF48t_u52f * z, burnsideF48t_u52Xh.mul_mem burnsideF48t_u52e_f_mem z.2⟩ h
      have e : z = ⟨burnsideF48t_u52f, burnsideF48t_u52e_f_mem⟩ *
          ⟨burnsideF48t_u52f * z, burnsideF48t_u52Xh.mul_mem burnsideF48t_u52e_f_mem z.2⟩ := by
        apply Subtype.ext
        show (z : Equiv.Perm (Fin 462)) = burnsideF48t_u52f * (burnsideF48t_u52f * z)
        rw [burnsideF48t_u52e_ffx]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hfP) h2
  K_le := burnsideF48t_u52e_Kh_le (by norm_num)
  KW_let := by
    have h : ∀ w ∈ burnsideF48t_u52eKhW.getD 2 [], ∀ l ∈ w, l.1 ≠ 3 := by decide
    exact h
  KW_cov := fun c hc => by
    have hc' : (c : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52eK' 2 := hc
    obtain ⟨m, hm, he⟩ := burnsideF48t_u52e_KL_cases (by norm_num)
      (burnsideF48t_u52e_KL_of_mem (by norm_num) hc')
    have hlen : m < (burnsideF48t_u52eKhW.getD 2 []).length := by
      rw [burnsideF48t_u52e_KhW_length (by norm_num)]
      exact hm
    refine ⟨(burnsideF48t_u52eKhW.getD 2 []).getD m [], ?_, Subtype.ext ?_⟩
    · rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem _
    · rw [burnsideF48t_u52e_coe_ev, he]
      rfl
  XW_let := by
    have h : ∀ w ∈ burnsideF48t_u52eXW, ∀ l ∈ w, l.1 ≠ 3 := by decide
    exact h
  YW_let := by
    have h : ∀ w ∈ burnsideF48t_u52eYW, ∀ l ∈ w, l.1 ≠ 2 := by decide
    exact h
  xred := fun x hx hx2 hxK hxx => by
    have hx0 := (burnsideF48t_u52e_mem_P1 x).1 hx
    have hxB : (x : Equiv.Perm (Fin 462)) burnsideF48t_u52pB ≠ burnsideF48t_u52pB :=
      fun h => hx2 ((burnsideF48t_u52e_mem_P2 x).2 h)
    obtain ⟨hK, hxx'⟩ := burnsideF48t_u52e_lift (by norm_num) hxK hxx
    obtain ⟨w, hw, hk⟩ := (burnsideF48t_u52e_tests1 x.2 hx0 hxB).2 hK hxx'
    refine ⟨w, hw, ?_⟩
    show (((burnsideF48s_ev burnsideF48t_u52eL w)⁻¹ * x :
      ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52eK' 2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_u52e_coe_ev]
    exact hk
  yred := fun y hy hy1 hyK hyy => by
    have hy0 := (burnsideF48t_u52e_mem_P2 y).1 hy
    have hyA : (y : Equiv.Perm (Fin 462)) burnsideF48t_u52pA ≠ burnsideF48t_u52pA :=
      fun h => hy1 ((burnsideF48t_u52e_mem_P1 y).2 h)
    obtain ⟨hK, hyy'⟩ := burnsideF48t_u52e_lift (by norm_num) hyK hyy
    obtain ⟨w, hw, hk⟩ := (burnsideF48t_u52e_tests2 y.2 hy0 hyA).1 hK hyy'
    refine ⟨w, hw, ?_⟩
    show (((burnsideF48s_ev burnsideF48t_u52eL w)⁻¹ * y :
      ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52eK' 2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_u52e_coe_ev]
    exact hk
  cand := fun u hu v hv c hc hcomm => by
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.1 hu
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hv
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.1 hc
    have hi4 : i < 4 := by simpa [burnsideF48t_u52eXW] using hi
    have hj2 : j < 2 := by simpa [burnsideF48t_u52eYW] using hj
    have hk18 : k < 18 := by rwa [burnsideF48t_u52e_KhW_length (by norm_num)] at hk
    have eu : u = burnsideF48t_u52eXW.getD i [] := by rw [List.getD_eq_getElem _ _ hi, hiu]
    have ev : v = burnsideF48t_u52eYW.getD j [] := by rw [List.getD_eq_getElem _ _ hj, hjv]
    have ec : c = (burnsideF48t_u52eKhW.getD 2 []).getD k [] := by
      rw [List.getD_eq_getElem _ _ hk, hkc]
    subst eu ev ec
    have hcomm' := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, burnsideF48t_u52e_coe_ev] at hcomm'
    rcases burnsideF48t_u52e_cand hi4 hj2 hk18 with ⟨t, ht, rfl, rfl, rfl, hrel⟩ | hne
    · obtain ⟨hfin, hcard⟩ := burnsideF48t_u52e_tc ht
      have hn : t.2.2.2 = 1 ∨ t.2.2.2 = 165 := by
        have : ∀ s ∈ burnsideF48t_u52eCands, s.2.2.2 = 1 ∨ s.2.2.2 = 165 := by decide
        exact this t ht
      refine ⟨hfin, ?_⟩
      rcases hn with h1 | h165
      · left
        rw [h1, one_mul] at hcard
        rw [burnsideF48t_u52e_card_Xh]
        exact lt_of_le_of_lt hcard (by norm_num)
      · right
        refine ⟨by rw [burnsideF48t_u52e_card_Xh]; rw [h165] at hcard; exact hcard, ?_⟩
        apply Subtype.ext
        rw [burnsideF48t_u52e_coe_ev]
        exact hrel h165
    · exact absurd hcomm' hne

end Engine

end CFSG.ASVolI
