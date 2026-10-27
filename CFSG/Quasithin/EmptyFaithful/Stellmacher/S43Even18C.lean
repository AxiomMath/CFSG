module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even18B

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace C18

private theorem fix_S5Syl_stabF : ∀ w : orth.W, (∀ σ ∈ S5SylF, orth.act σ w = w) →
    ∀ σ : Perm (Fin 5), σ 4 = 4 → orth.act σ w = w := by
  decide +kernel

private theorem comm_S5Syl_invF : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    ∀ w ∈ spanF (commGensF orth S5SylF Finset.univ),
      orth.act σ w ∈ spanF (commGensF orth S5SylF Finset.univ) := by
  decide +kernel

theorem fixW_S5Syl_le {K : Subgroup (Perm (Fin 5))}
    (hK : K ≤ MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)) :
    fixW orth S5Syl ≤ fixW orth K := fun w hw σ hσ =>
  fix_S5Syl_stabF w (fun τ hτ => hw τ ((mem_S5Syl_iff τ).mpr hτ)) σ
    (MulAction.mem_stabilizer_iff.mp (hK hσ))

theorem commW_S5Syl_inv {σ : Perm (Fin 5)} (hσ : σ 4 = 4) :
    ∀ w ∈ commW orth S5Syl ⊤, orth.act σ w ∈ commW orth S5Syl ⊤ := by
  have hmem := fun w => mem_commW_iff orth mem_S5Syl_iff (U := ⊤) (Uf := Finset.univ)
    (fun u => by simp) w
  intro w hw
  rw [hmem] at hw ⊢
  exact comm_S5Syl_invF σ hσ w hw

variable {G : Type} [Group G] {H M S : Subgroup G}

theorem le_normalizer_commutator {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  refine Sit43.le_normalizer_of_conj_mem fun x hx y hy => ?_
  have hmap : (⁅A, B⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ ⁅A, B⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hA hx) a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hB hx) b).mp hb
  exact hmap ⟨y, hy, rfl⟩

variable [Finite G] {α β : Geo H M}

omit [Finite G] in
theorem Vst_le_Qv (hs : Sit43 α) (hβ : β ∈ nbrs α) : Vst β ≤ Qv β := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have ha' : a ∈ Qv β := hs.Vn_le_Qv hβ ha
  rw [commutatorElement_def]
  exact (Qv β).mul_mem ((Qv β).mul_mem ((Qv β).mul_mem ha' hb) ((Qv β).inv_mem ha'))
    ((Qv β).inv_mem hb)

omit [Finite G] in
theorem stab_le_normalizer_Vst (β : Geo H M) :
    stab β ≤ Subgroup.normalizer (Vst β : Set G) :=
  le_normalizer_commutator (stab_le_normalizer_Vn β) (le_normalizer_pCoreOf 2 (stab β))

theorem comm_Vst_edge_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (hD4 : Nat.card (Vn β) = 2 ^ 6) :
    ∀ g ∈ stab α ⊓ stab β, ∀ u ∈ Vst β, g * u * g⁻¹ * u⁻¹ ∈ Zv α := by
  intro g hg u hu
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ := nbrs_symm hβ
  have hrel : (Zv α).relIndex (Vst β) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (Zv α) (Vst β)
    rw [inf_comm, hs.Vst_inf_Zv hA h26 hb hβv hαβ hD4, hs.card_comm_Qv hA h26 hβv hαβ,
      hs.card_Vst hA h26 hb hβv hD4] at h1
    omega
  have hgV : g * u * g⁻¹ ∈ Vst β :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vst β hg.2) u).mp hu
  have hZn := stab_le_normalizer_Zv hA α
  have huα : u ∈ stab α := (Qv_le_stab_of_mem_nbrs hA hαβ) (Vst_le_Qv hs hβ hu)
  by_cases huZ : u ∈ Zv α
  · exact (Zv α).mul_mem ((Subgroup.mem_normalizer_iff.mp (hZn hg.1) u).mp huZ)
      ((Zv α).inv_mem huZ)
  · have hgu : g * u * g⁻¹ ∉ Zv α := fun h => huZ (by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hZn ((stab α).inv_mem hg.1)) _).mp h
      simpa [mul_assoc] using h1)
    have h1 := inv_mul_mem_of_relIndex_two hrel hu hgV huZ hgu
    have h2 := (Subgroup.mem_normalizer_iff.mp (hZn huα) _).mp h1
    have e : u * (u⁻¹ * (g * u * g⁻¹)) * u⁻¹ = g * u * g⁻¹ * u⁻¹ := by group
    rwa [e] at h2

theorem fixSecIn_edge_le_Mab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {N : Subgroup G} (hN : IsOrthSec (stab α) (Zv α) N) (hZN : Zv α ≤ N)
    (hNs : N ≤ stab α) :
    fixSecIn (stab α ⊓ stab β) (Zv α) N ≤ fixSecIn (Mab α β) (Zv α) N := by
  obtain ⟨hn, Ψ, β', hΨs, hkΨ, hsd, hPS, -⟩ := exists_normalized_orth hA h26 hs hβ hN
  have hMs : Mab α β ≤ stab α := Mab_le_stab α β
  have hSM : S5Syl ≤ ((Mab α β).subgroupOf (stab α)).map Ψ := by
    rw [← hPS]
    exact Subgroup.map_mono (fun x hx => hs.stab_inf_le_Mab hA hβ hx)
  have hMle : ((Mab α β).subgroupOf (stab α)).map Ψ ≤
      MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5) := by
    rcases le_stab_four_or_eq_top hSM with h | h
    · exact h
    · exfalso
      apply hs.Mab_ne_stab hA hβ
      refine le_antisymm hMs fun x hx => ?_
      have hmem : Ψ ⟨x, hx⟩ ∈ ((Mab α β).subgroupOf (stab α)).map Ψ := h ▸ Subgroup.mem_top _
      obtain ⟨m, hm, hmx⟩ := hmem
      have hq : (m⁻¹ * ⟨x, hx⟩ : ↥(stab α)) ∈ Ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
      rw [hkΨ, Subgroup.mem_subgroupOf] at hq
      have hqM : ((m⁻¹ * ⟨x, hx⟩ : ↥(stab α)) : G) ∈ Mab α β := hs.Qv_le_Mab hA hβ hq
      have e : x = (m : G) * ((m⁻¹ * ⟨x, hx⟩ : ↥(stab α)) : G) := by simp
      rw [e]
      exact (Mab α β).mul_mem (Subgroup.mem_subgroupOf.mp hm) hqM
  have hNZ : N ≤ Subgroup.normalizer (Zv α : Set G) := hNs.trans (stab_le_normalizer_Zv hA α)
  intro y hy
  have hyN : y ∈ N := ((mem_fixSecIn_iff hNZ).mp hy).1
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨y, hyN⟩ : ↥N))
  have h1 := (mem_fixSecIn_iff_of_secData hsd hZN inf_le_left hu).mp hy
  rw [hPS] at h1
  exact (mem_fixSecIn_iff_of_secData hsd hZN hMs hu).mpr (fixW_S5Syl_le hMle h1)

theorem comm_Vst_Mab_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) (hD4 : Nat.card (Vn β) = 2 ^ 6) {N : Subgroup G}
    (hN : IsOrthSec (stab α) (Zv α) N) (hZN : Zv α ≤ N) (hNs : N ≤ stab α)
    (hVN : Vst β ≤ N) : ∀ m ∈ Mab α β, ∀ u ∈ Vst β, m * u * m⁻¹ * u⁻¹ ∈ Zv α := by
  intro m hm u hu
  have hNZ : N ≤ Subgroup.normalizer (Zv α : Set G) := hNs.trans (stab_le_normalizer_Zv hA α)
  have h1 : u ∈ fixSecIn (stab α ⊓ stab β) (Zv α) N := (mem_fixSecIn_iff hNZ).mpr
    ⟨hVN hu, fun g hg => comm_Vst_edge_mem hA h26 hs hb hβ hD4 g hg u hu⟩
  exact ((mem_fixSecIn_iff hNZ).mp (fixSecIn_edge_le_Mab hA h26 hs hβ hN hZN hNs h1)).2 m hm

theorem Mab_le_normalizer_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) :
    Mab α β ≤ Subgroup.normalizer ((⁅Zv α, Qv β⁆ : Subgroup G) : Set G) := by
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  rw [hs.comm_Qv_eq hA h26 hβv (nbrs_symm hβ), D.comm_eq]
  intro m hm
  have hmX : m ∈ stab α := Mab_le_stab α β hm
  have h4 : D.ψ ⟨m, hmX⟩ 4 = 4 := (Sit43.mem_Mab_iff D ⟨m, hmX⟩).mp hm
  exact (D.mem_normalizer_map_iff _ ⟨m, hmX⟩).mpr (commW_S5Syl_inv h4)

section Norm

variable (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) (hb : 3 ≤ bMin H M)
  (hβ : β ∈ nbrs α) (hD4 : Nat.card (Vn β) = 2 ^ 6) {N : Subgroup G}
  (hN : IsOrthSec (stab α) (Zv α) N) (hZN : Zv α ≤ N) (hNs : N ≤ stab α) (hVN : Vst β ≤ N)

include hA h26 hs hb hβ hD4 hN hZN hNs hVN

theorem sq_conj_mem_Vst {m : G} (hm : m ∈ Mab α β) :
    ∀ u ∈ Vst β, m ^ 2 * u * (m ^ 2)⁻¹ ∈ Vst β := by
  intro u hu
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ := nbrs_symm hβ
  have hBV : ⁅Zv α, Qv β⁆ = Vst β ⊓ Zv α := (hs.Vst_inf_Zv hA h26 hb hβv hαβ hD4).symm
  have hBZ : ⁅Zv α, Qv β⁆ ≤ Zv α := hBV ▸ inf_le_right
  have hB2 : (⁅Zv α, Qv β⁆ : Subgroup G).relIndex (Zv α) = 2 := by
    have h1 := Subgroup.relIndex_mul_card ⁅Zv α, Qv β⁆ (Zv α)
    rw [inf_eq_left.mpr hBZ, hs.card_comm_Qv hA h26 hβv hαβ, hs.card_Zv_false hs.vα] at h1
    omega
  have hmX : m ∈ stab α := Mab_le_stab α β hm
  have hc := comm_Vst_Mab_mem hA h26 hs hb hβ hD4 hN hZN hNs hVN m hm u hu
  have hBn := Mab_le_normalizer_comm hA h26 hs hβ
  have hZn := stab_le_normalizer_Zv hA α
  have hd : m * (m * u * m⁻¹ * u⁻¹) * m⁻¹ * (m * u * m⁻¹ * u⁻¹) ∈ ⁅Zv α, Qv β⁆ := by
    by_cases hcB : m * u * m⁻¹ * u⁻¹ ∈ ⁅Zv α, Qv β⁆
    · exact (⁅Zv α, Qv β⁆ : Subgroup G).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hBn hm) _).mp hcB) hcB
    · have hmc : m * (m * u * m⁻¹ * u⁻¹) * m⁻¹ ∈ Zv α :=
        (Subgroup.mem_normalizer_iff.mp (hZn hmX) _).mp hc
      have hmcB : (m * (m * u * m⁻¹ * u⁻¹) * m⁻¹)⁻¹ ∉ ⁅Zv α, Qv β⁆ := fun h => hcB (by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hBn ((Mab α β).inv_mem hm)) _).mp
          ((⁅Zv α, Qv β⁆ : Subgroup G).inv_mem h)
        simpa [mul_assoc] using h1)
      have h1 := inv_mul_mem_of_relIndex_two hB2 ((Zv α).inv_mem hmc) hc hmcB hcB
      simpa using h1
  have e : m ^ 2 * u * (m ^ 2)⁻¹ =
      (m * (m * u * m⁻¹ * u⁻¹) * m⁻¹ * (m * u * m⁻¹ * u⁻¹)) * u := by
    rw [pow_two]; group
  rw [e]
  exact (Vst β).mul_mem (hBV ▸ hd).1 hu

theorem mem_normalizer_Vst_of_odd {o : G} (ho : o ∈ Mab α β) {k : ℕ} (hk : Odd k)
    (hok : o ^ k = 1) : o ∈ Subgroup.normalizer (Vst β : Set G) := by
  have h2 : o ^ 2 ∈ Subgroup.normalizer (Vst β : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨sq_conj_mem_Vst hA h26 hs hb hβ hD4 hN hZN hNs hVN ho x, fun hx => ?_⟩
    have h1 := sq_conj_mem_Vst hA h26 hs hb hβ hD4 hN hZN hNs hVN ((Mab α β).inv_mem ho) _ hx
    have e : o⁻¹ ^ 2 * (o ^ 2 * x * (o ^ 2)⁻¹) * (o⁻¹ ^ 2)⁻¹ = x := by group
    rwa [e] at h1
  obtain ⟨j, rfl⟩ := hk
  have e : o = (o ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, pow_succ, hok, one_mul]
  rw [e]
  exact Subgroup.pow_mem _ h2 _

theorem Mab_le_normalizer_Vst : Mab α β ≤ Subgroup.normalizer (Vst β : Set G) := by
  set T : Subgroup G := stab α ⊓ stab β with hT
  set K : Subgroup G := Mab α β ⊓ Subgroup.normalizer (Vst β : Set G) with hK
  have hTM : T ≤ Mab α β := hs.stab_inf_le_Mab hA hβ
  have hMs : Mab α β ≤ stab α := Mab_le_stab α β
  have hTK : T ≤ K := le_inf hTM (inf_le_right.trans (stab_le_normalizer_Vst β))
  have hQT : Qv α ≤ T := le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA hβ)
  have e1 := Subgroup.relIndex_mul_relIndex (Qv α) T (stab α) hQT inf_le_left
  have e2 := Subgroup.relIndex_mul_relIndex T (Mab α β) (stab α) hTM hMs
  rw [hs.relIndex_Qv_edge_stab hA hβ, hs.relIndex_Qv_stab_five hA hβ] at e1
  rw [hs.relIndex_Mab hA hβ] at e2
  have h3 : T.relIndex (Mab α β) = 3 := by omega
  have h3dvd : 3 ∣ Nat.card (Mab α β) := h3 ▸ Subgroup.relIndex_dvd_card _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hx3 : (x : G) ^ 3 = 1 := by
    rw [← hx, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have hxK : (x : G) ∈ K := ⟨x.2, mem_normalizer_Vst_of_odd hA h26 hs hb hβ hD4 hN hZN hNs hVN
    x.2 (by decide) hx3⟩
  have hxT : (x : G) ∉ T := by
    intro h
    have hp : IsPGroup 2 ↥T := (sylow_stab_inf_left hA hβ).2.1
    obtain ⟨k, hk⟩ := hp ⟨x, h⟩
    have hdvd : orderOf (⟨(x : G), h⟩ : ↥T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by decide)
  have e3 := Subgroup.relIndex_mul_relIndex T K (Mab α β) hTK inf_le_left
  rw [h3] at e3
  have hdvd : T.relIndex K ∣ 3 := Dvd.intro _ e3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact absurd ((Subgroup.relIndex_eq_one.mp h1) hxK) hxT
  · have h2 : K.relIndex (Mab α β) = 1 := by rw [h1] at e3; omega
    exact (Subgroup.relIndex_eq_one.mp h2).trans inf_le_right

end Norm

end C18

end CFSG.Quasithin.F53.Stellmacher.S43.Even
