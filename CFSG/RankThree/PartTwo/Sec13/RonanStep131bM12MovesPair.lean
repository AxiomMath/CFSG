module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesD
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesElem
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem mem_normalizer_centralizer_of_inv {G : Type} [Group G] {c t : G}
    (ht : t * c * t⁻¹ = c⁻¹) :
    t ∈ Subgroup.normalizer (Subgroup.centralizer ({c} : Set G) : Set G) := by
  have key : ∀ g : G, g * c⁻¹ * g⁻¹ = c → ∀ x ∈ Subgroup.centralizer ({c} : Set G),
      g * x * g⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hxc' : x * c⁻¹ = c⁻¹ * x := (Commute.inv_right (show Commute x c from hx)).eq
    calc g * x * g⁻¹ * c = g * x * g⁻¹ * (g * c⁻¹ * g⁻¹) := by rw [hg]
      _ = g * (x * c⁻¹) * g⁻¹ := by group
      _ = g * (c⁻¹ * x) * g⁻¹ := by rw [hxc']
      _ = (g * c⁻¹ * g⁻¹) * (g * x * g⁻¹) := by group
      _ = c * (g * x * g⁻¹) := by rw [hg]
  have hc2 : t * c⁻¹ * t⁻¹ = c := by
    calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
      _ = c⁻¹⁻¹ := by rw [ht]
      _ = c := inv_inv c
  have hc3 : t⁻¹ * c⁻¹ * t⁻¹⁻¹ = c := by
    calc t⁻¹ * c⁻¹ * t⁻¹⁻¹ = t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ := by rw [ht]
      _ = c := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t hc2 x
  · intro hx
    have h := key t⁻¹ hc3 _ hx
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem mem_normalizer_thetaC_of_inv {G : Type} [Group G] [Finite G] {c t : G}
    (ht : t * c * t⁻¹ = c⁻¹) : t ∈ Subgroup.normalizer (thetaC c : Set G) := by
  have hN := mem_normalizer_centralizer_of_inv ht
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact Sec12.conj_mem_inSubgroup_theta hN hu
  · intro hu
    have h : t⁻¹ * (t * u * t⁻¹) * t⁻¹⁻¹ ∈ thetaC c :=
      Sec12.conj_mem_inSubgroup_theta (inv_mem hN) hu
    have e : t⁻¹ * (t * u * t⁻¹) * t⁻¹⁻¹ = u := by group
    rwa [e] at h

theorem conj_mul_mem_aux {G : Type} [Group G] {Θ : Subgroup G} {t v y θ : G}
    (ht : t ∈ Subgroup.normalizer (Θ : Set G)) (hv : v ∈ Subgroup.normalizer (Θ : Set G))
    (hy : y⁻¹ ∈ Subgroup.normalizer (Θ : Set G)) (hθ : θ ∈ Θ)
    (hty : t * y * t⁻¹ = y⁻¹) (hvy : v * y⁻¹ * v⁻¹ = y⁻¹) :
    v * (t * (θ * y) * t⁻¹) * v⁻¹ * (θ * y) ∈ Θ := by
  have hconj : ∀ g ∈ Subgroup.normalizer (Θ : Set G), ∀ u ∈ Θ, g * u * g⁻¹ ∈ Θ :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have e : v * (t * (θ * y) * t⁻¹) * v⁻¹ * (θ * y) =
      (v * (t * θ * t⁻¹) * v⁻¹) * (y⁻¹ * θ * y) := by
    calc v * (t * (θ * y) * t⁻¹) * v⁻¹ * (θ * y)
        = v * ((t * θ * t⁻¹) * (t * y * t⁻¹)) * v⁻¹ * (θ * y) := by group
      _ = v * ((t * θ * t⁻¹) * y⁻¹) * v⁻¹ * (θ * y) := by rw [hty]
      _ = (v * (t * θ * t⁻¹) * v⁻¹) * (v * y⁻¹ * v⁻¹) * (θ * y) := by group
      _ = (v * (t * θ * t⁻¹) * v⁻¹) * y⁻¹ * (θ * y) := by rw [hvy]
      _ = (v * (t * θ * t⁻¹) * v⁻¹) * (y⁻¹ * θ * y) := by group
  rw [e]
  refine mul_mem (hconj v hv _ (hconj t ht θ hθ)) ?_
  have h := hconj _ hy θ hθ
  rwa [inv_inv] at h

theorem conj_mul_mem_of_mem_zpowers_sup {G : Type} [Group G] {Θ : Subgroup G} {c t v : G}
    (hc : c ∈ Subgroup.normalizer (Θ : Set G)) (ht : t ∈ Subgroup.normalizer (Θ : Set G))
    (hv : v ∈ Subgroup.normalizer (Θ : Set G)) (htc : t * c * t⁻¹ = c⁻¹) (hvc : v * c = c * v)
    {z : G} (hz : z ∈ Subgroup.zpowers c ⊔ Θ) : v * (t * z * t⁻¹) * v⁻¹ * z ∈ Θ := by
  rw [sup_comm] at hz
  obtain ⟨θ, hθ, y, hy, rfl⟩ := exists_mul_of_mem_sup (Subgroup.zpowers_le.mpr hc) hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hty : t * c ^ k * t⁻¹ = (c ^ k)⁻¹ := by
    have h := map_zpow (MulAut.conj t) c k
    simp only [MulAut.conj_apply] at h
    rw [h, htc, inv_zpow]
  have hvy : v * (c ^ k)⁻¹ * v⁻¹ = (c ^ k)⁻¹ := by
    have h : Commute v c := hvc
    have h2 : Commute v (c ^ k)⁻¹ := (h.zpow_right k).inv_right
    calc v * (c ^ k)⁻¹ * v⁻¹ = (c ^ k)⁻¹ * v * v⁻¹ := by rw [h2.eq]
      _ = (c ^ k)⁻¹ := by group
  exact conj_mul_mem_aux ht hv (inv_mem (zpow_mem hc k)) hθ hty hvy

theorem s2pair_of_parts (hswap : S2swap) (ha : S2a) (hfus : S2fus) : S2pair := by
  intro G _ _ A c L E F a b R Y hY _ _ t EY hd htL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hmapL, hne, h3, -, -⟩ := hswap G A c L E F a b R Y hY t EY hd htL
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hY.hCfg
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨-, -, -, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hL := hD.mem_thetaComponentsAt
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcE := hY.hcE
  have hbE := hY.hbE
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEC' : E ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx c hcE)
  have hNΘ := centralizer_le_normalizer_thetaC (G := G) c
  have hEN : E ≤ Subgroup.normalizer (thetaC c : Set G) := fun x hx => hNΘ (hEC' hx)
  have hcN : c ∈ Subgroup.normalizer (thetaC c : Set G) := hEN hcE
  have hconj : ∀ g ∈ Subgroup.normalizer (thetaC c : Set G), ∀ u ∈ thetaC c,
      g * u * g⁻¹ ∈ thetaC c := fun g hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have htc : t * c * t⁻¹ = c⁻¹ := hd.inv c hd.mem_c
  have htΘ : t ∈ Subgroup.normalizer (thetaC c : Set G) := mem_normalizer_thetaC_of_inv htc
  have hc2 : t * c⁻¹ * t⁻¹ = c := by
    calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
      _ = c⁻¹⁻¹ := by rw [htc]
      _ = c := inv_inv c
  have htb : t * b = b * t := hd.comm_b
  have htb' : t⁻¹ * b * t = b := by
    calc t⁻¹ * b * t = t⁻¹ * (b * t) * 1 := by group
      _ = t⁻¹ * (t * b) := by rw [← htb]; group
      _ = b := by group
  have htb'' : b⁻¹ * t⁻¹ * b = t⁻¹ := by
    have h : b⁻¹ * t⁻¹ * b = (b⁻¹ * t⁻¹ * b * t) * t⁻¹ := by group
    have h2 : b⁻¹ * t⁻¹ * b * t = 1 := by
      calc b⁻¹ * t⁻¹ * b * t = b⁻¹ * (t⁻¹ * b * t) := by group
        _ = 1 := by rw [htb']; group
    rw [h, h2, one_mul]
  obtain ⟨v, hvL, hv3, hvP1, hvP2, y0, hy0, hy0n⟩ := hfus G A c L E hY.hCfg
  have hvC : v * c = c * v :=
    Subgroup.mem_centralizer_singleton_iff.mp (hLC hvL)
  have hvN : v ∈ Subgroup.normalizer (thetaC c : Set G) := hNΘ (hLC hvL)
  have hv'L : t * v * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨v, hvL, by simp [MulAut.conj_apply]⟩
  have hEconj : ∀ e ∈ E, ∀ z ∈ Subgroup.zpowers c ⊔ thetaC c,
      e * z * e⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c := by
    intro e he z hz
    refine conj_mem_zpowers_sup (hNΘ (hEC' he)) ?_ hz
    have h1 : e * c * e⁻¹ * c⁻¹ = 1 := by
      rw [hEcomm e he c hcE]
      group
    rw [h1]
    exact one_mem _
  have hP₂N : (E ⊓ L) ≤ Subgroup.normalizer
      ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    have : x * p * x⁻¹ = p := by
      rw [hEcomm x hx.1 p hp.1]
      group
    rw [this]
    exact hp
  have hvE : ∀ e ∈ E, v * e * v⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ thetaC c := by
    intro e he
    have he' : e ∈ (E ⊓ Sec4.thetaQuotCentralizer L) ⊔ (E ⊓ L) := by rw [hsup]; exact he
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := exists_mul_of_mem_sup hP₂N he'
    have e1 : v * (p₁ * p₂) * v⁻¹ * (p₁ * p₂)⁻¹ =
        (v * p₁ * v⁻¹ * p₁⁻¹) * (p₁ * (v * p₂ * v⁻¹ * p₂⁻¹) * p₁⁻¹) := by group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_right (hvP1 p₁ hp₁)) (hEconj p₁ hp₁.1 _ (hvP2 p₂ hp₂))
  have hv'E : ∀ e ∈ E, (t * v * t⁻¹) * e * (t * v * t⁻¹)⁻¹ * e⁻¹ ∈
      Subgroup.zpowers c ⊔ thetaC c := by
    intro e he
    have heE : t⁻¹ * e * t⁻¹⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hd.mem_normalizer) e).mp he
    have e1 : (t * v * t⁻¹) * e * (t * v * t⁻¹)⁻¹ * e⁻¹ =
        t * (v * (t⁻¹ * e * t⁻¹⁻¹) * v⁻¹ * (t⁻¹ * e * t⁻¹⁻¹)⁻¹) * t⁻¹ := by group
    rw [e1]
    refine conj_mem_zpowers_sup htΘ ?_ (hvE _ heE)
    rw [htc]
    exact Subgroup.mem_sup_left (mul_mem (inv_mem (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c)))
  have hv'C : t * v * t⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvc' : v * c⁻¹ = c⁻¹ * v := (Commute.inv_right (show Commute v c from hvC)).eq
    calc t * v * t⁻¹ * c = t * v * t⁻¹ * (t * c⁻¹ * t⁻¹) := by rw [hc2]
      _ = t * (v * c⁻¹) * t⁻¹ := by group
      _ = t * (c⁻¹ * v) * t⁻¹ := by rw [hvc']
      _ = (t * c⁻¹ * t⁻¹) * (t * v * t⁻¹) := by group
      _ = c * (t * v * t⁻¹) := by rw [hc2]
  have hv'3 : (t * v * t⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hv3]
    simp
  have hbmain : (v * (t * v * t⁻¹)) * b * (v * (t * v * t⁻¹))⁻¹ * b⁻¹ ∈ thetaC c := by
    have e1 : (v * (t * v * t⁻¹)) * b * (v * (t * v * t⁻¹))⁻¹ * b⁻¹ =
        (v * (t * (v * b * v⁻¹ * b⁻¹) * t⁻¹) * v⁻¹) * (v * b * v⁻¹ * b⁻¹) := by
      calc (v * (t * v * t⁻¹)) * b * (v * (t * v * t⁻¹))⁻¹ * b⁻¹
          = v * t * v * (t⁻¹ * b * t) * v⁻¹ * t⁻¹ * v⁻¹ * b⁻¹ := by group
        _ = v * t * v * b * v⁻¹ * t⁻¹ * v⁻¹ * b⁻¹ := by rw [htb']
        _ = v * t * v * b * v⁻¹ * (b⁻¹ * t⁻¹ * b) * v⁻¹ * b⁻¹ := by rw [htb'']
        _ = (v * (t * (v * b * v⁻¹ * b⁻¹) * t⁻¹) * v⁻¹) * (v * b * v⁻¹ * b⁻¹) := by group
    rw [e1]
    exact conj_mul_mem_of_mem_zpowers_sup hcN htΘ hvN htc hvC (hvE b hbE)
  have hnot : v * (t * v * t⁻¹) ∉ E ⊔ thetaC c := by
    intro hmem
    rw [sup_comm] at hmem
    obtain ⟨θ, hθ, e, he, hθe⟩ := exists_mul_of_mem_sup hEN hmem
    have hy1 : t * y0 * t⁻¹ ∈ E ⊓ Sec4.thetaQuotCentralizer L := h3 y0 hy0
    have hy1E : t * y0 * t⁻¹ ∈ E := hy1.1
    have hA : (v * (t * v * t⁻¹)) * (t * y0 * t⁻¹) * (v * (t * v * t⁻¹))⁻¹ *
        (t * y0 * t⁻¹)⁻¹ ∈ thetaC c := by
      rw [hθe]
      have hyc : e * (t * y0 * t⁻¹) * e⁻¹ = t * y0 * t⁻¹ := by
        rw [hEcomm e he _ hy1E]
        group
      have e1 : (θ * e) * (t * y0 * t⁻¹) * (θ * e)⁻¹ * (t * y0 * t⁻¹)⁻¹ =
          θ * (e * (t * y0 * t⁻¹) * e⁻¹) * θ⁻¹ * (t * y0 * t⁻¹)⁻¹ := by group
      rw [e1, hyc]
      have e2 : θ * (t * y0 * t⁻¹) * θ⁻¹ * (t * y0 * t⁻¹)⁻¹ =
          θ * ((t * y0 * t⁻¹) * θ⁻¹ * (t * y0 * t⁻¹)⁻¹) := by group
      rw [e2]
      exact mul_mem hθ ((Subgroup.mem_normalizer_iff.mp (hEN hy1E) θ⁻¹).mp (inv_mem hθ))
    have hB : v * (t * y0 * t⁻¹) * v⁻¹ * (t * y0 * t⁻¹)⁻¹ ∈ thetaC c := hvP1 _ hy1
    have e3 : (v * (t * v * t⁻¹)) * (t * y0 * t⁻¹) * (v * (t * v * t⁻¹))⁻¹ *
        (t * y0 * t⁻¹)⁻¹ =
        (v * (t * (v * y0 * v⁻¹ * y0⁻¹) * t⁻¹) * v⁻¹) *
          (v * (t * y0 * t⁻¹) * v⁻¹ * (t * y0 * t⁻¹)⁻¹) := by group
    rw [e3] at hA
    have hC : v * (t * (v * y0 * v⁻¹ * y0⁻¹) * t⁻¹) * v⁻¹ ∈ thetaC c := by
      have h := mul_mem hA (inv_mem hB)
      have e4 : (v * (t * (v * y0 * v⁻¹ * y0⁻¹) * t⁻¹) * v⁻¹) *
          (v * (t * y0 * t⁻¹) * v⁻¹ * (t * y0 * t⁻¹)⁻¹) *
          (v * (t * y0 * t⁻¹) * v⁻¹ * (t * y0 * t⁻¹)⁻¹)⁻¹ =
          v * (t * (v * y0 * v⁻¹ * y0⁻¹) * t⁻¹) * v⁻¹ := by group
      rwa [e4] at h
    have hD' : t * (v * y0 * v⁻¹ * y0⁻¹) * t⁻¹ ∈ thetaC c :=
      (Subgroup.mem_normalizer_iff.mp hvN _).mpr hC
    exact hy0n ((Subgroup.mem_normalizer_iff.mp htΘ _).mpr hD')
  have hvv' : v * (t * v * t⁻¹) * v⁻¹ * (t * v * t⁻¹)⁻¹ ∈ thetaC c :=
    ha G c L _ hL hmapL hne.symm v hvL _ hv'L
  have hv'L' : ∀ l ∈ L, (t * v * t⁻¹) * l * (t * v * t⁻¹)⁻¹ * l⁻¹ ∈ thetaC c := fun l hl =>
    ha G c _ L hmapL hL hne _ hv'L l hl
  exact ⟨v, t * v * t⁻¹, hvL, hv'C, hv3, hv'3, hvv', hv'L', hvE, hv'E, hbmain, hnot⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
