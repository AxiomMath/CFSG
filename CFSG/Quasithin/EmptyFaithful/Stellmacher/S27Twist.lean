module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Untwist
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27LiftDef
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem sign_eq_one_of_mem_oTwoRes {X : Subgroup G} (ψ : ↥X →* Perm (Fin 5)) {x : G}
    (hx : x ∈ oTwoRes X) : Perm.sign (ψ ⟨x, oTwoRes_le X hx⟩) = 1 := by
  set E : Subgroup G := ((alternatingGroup (Fin 5)).comap ψ).map X.subtype with hE
  have hle : oTwoRes X ≤ E := by
    refine (Subgroup.closure_le E).mpr ?_
    rintro g ⟨hgX, m, hm, hgm⟩
    refine ⟨⟨g, hgX⟩, ?_, rfl⟩
    show ψ ⟨g, hgX⟩ ∈ alternatingGroup (Fin 5)
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : ψ ⟨g, hgX⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨g, hgX⟩ : ↥X) ^ m = 1 := Subtype.ext (by simpa using hgm)
      rw [this, map_one]
    have h2 : Perm.sign (ψ ⟨g, hgX⟩) ^ m = 1 := by rw [← map_pow, h1, map_one]
    rcases Int.units_eq_one_or (Perm.sign (ψ ⟨g, hgX⟩)) with h | h
    · exact h
    · rw [h, hm.neg_one_pow] at h2
      exact absurd h2 (by decide)
  obtain ⟨x', hx', hxx⟩ := hle hx
  have : x' = ⟨x, oTwoRes_le X hx⟩ := Subtype.ext hxx
  rw [← this]
  exact Equiv.Perm.mem_alternatingGroup.mp hx'

namespace Sit27

variable {α β : Geo H M}

theorem conj_comm_mem_Zv (hA : F53Amalgam H M S) (P : Sit27 α β)
    (htop : Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
      Set ↥(stab α)) = ⊤) :
    ∀ g ∈ stab α, ∀ y ∈ Zv α ⊔ Zv β, g * y * g⁻¹ * y⁻¹ ∈ Zv α := by
  have hZn : ∀ g ∈ stab α, ∀ a ∈ Zv α, g * a * g⁻¹ ∈ Zv α := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) a).mp ha
  have hYn : ∀ g ∈ stab α, ∀ y ∈ Zv α ⊔ Zv β, g * y * g⁻¹ ∈ Zv α ⊔ Zv β := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (P.norm hg) y).mp hy
  let T : Subgroup ↥(stab α) :=
    { carrier := {g | ∀ y ∈ Zv α ⊔ Zv β, (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ Zv α}
      one_mem' := fun y _ => by simp
      mul_mem' := fun {g₁ g₂} h₁ h₂ y hy => by
        have e : ((g₁ * g₂ : ↥(stab α)) : G) * y * ((g₁ * g₂ : ↥(stab α)) : G)⁻¹ * y⁻¹ =
            (g₁ : G) * ((g₂ : G) * y * (g₂ : G)⁻¹ * y⁻¹) * (g₁ : G)⁻¹ *
              ((g₁ : G) * y * (g₁ : G)⁻¹ * y⁻¹) := by
          simp only [Subgroup.coe_mul]; group
        rw [e]
        exact Subgroup.mul_mem _ (hZn _ g₁.2 _ (h₂ y hy)) (h₁ y hy)
      inv_mem' := fun {g} hg y hy => by
        have hy' := hYn _ (inv_mem g.2) y hy
        have e : ((g⁻¹ : ↥(stab α)) : G) * y * ((g⁻¹ : ↥(stab α)) : G)⁻¹ * y⁻¹ =
            ((g : G) * ((g : G)⁻¹ * y * (g : G)⁻¹⁻¹) * (g : G)⁻¹ *
              ((g : G)⁻¹ * y * (g : G)⁻¹⁻¹)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]; group
        rw [e]
        exact Subgroup.inv_mem _ (hg _ hy') }
  have hTn : T.Normal := ⟨fun g hg h y hy => by
    have hy' := hYn _ (inv_mem h.2) y hy
    have e : ((h * g * h⁻¹ : ↥(stab α)) : G) * y * ((h * g * h⁻¹ : ↥(stab α)) : G)⁻¹ * y⁻¹ =
        (h : G) * ((g : G) * ((h : G)⁻¹ * y * (h : G)⁻¹⁻¹) * (g : G)⁻¹ *
          ((h : G)⁻¹ * y * (h : G)⁻¹⁻¹)⁻¹) * (h : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact hZn _ h.2 _ (hg _ hy')⟩
  have hBT : (Qv β).subgroupOf (stab α) ≤ T := by
    intro d hd y hy
    have hd' : (d : G) ∈ Qv β := hd
    have hZβn : Zv β ≤ Subgroup.normalizer (Zv α : Set G) :=
      (P.Zv_right_le_Qv.trans (pCoreOf_le 2 _)).trans (stab_le_normalizer_Zv hA α)
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZβn).mp hy
    have hdb : (d : G) * b * (d : G)⁻¹ = b := by
      rw [Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hb).2 _ hd',
        mul_inv_cancel_right]
    have e : (d : G) * (a * b) * (d : G)⁻¹ * (a * b)⁻¹ = (d : G) * a * (d : G)⁻¹ * a⁻¹ := by
      calc (d : G) * (a * b) * (d : G)⁻¹ * (a * b)⁻¹
          = (d : G) * a * (d : G)⁻¹ * ((d : G) * b * (d : G)⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = (d : G) * a * (d : G)⁻¹ * a⁻¹ := by rw [hdb]; group
    rw [e]
    exact Subgroup.mul_mem _ (hZn _ d.2 _ ha) (Subgroup.inv_mem _ ha)
  have hLT := Subgroup.normalClosure_le_normal (N := T) (fun x hx => hBT hx)
  intro g hg y hy
  have hgT : (⟨g, hg⟩ : ↥(stab α)) ∈ T := hLT (by rw [htop]; exact Subgroup.mem_top _)
  exact hgT y hy

theorem conj_comm_Qv_eq (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β)
    (htop : Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
      Set ↥(stab α)) = ⊤) {z y : G} (hz : z ∈ Qv α) (hy : y ∈ Zv β) :
    ∀ g ∈ stab α, g * (z * y * z⁻¹ * y⁻¹) * g⁻¹ = z * y * z⁻¹ * y⁻¹ := by
  intro g hg
  have hcZ := P.conj_comm_mem_Zv hA htop
  have hyY : y ∈ Zv α ⊔ Zv β := Subgroup.mem_sup_right hy
  have hzs : z ∈ stab α := pCoreOf_le 2 _ hz
  have hZc : ∀ a ∈ Zv α, ∀ v ∈ Qv α, v * a = a * v := fun a ha v hv =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α ha).2 v hv
  have hNY : ∀ n ∈ Qv α ⊓ Qv β, ∀ v ∈ Zv α ⊔ Zv β, n * v = v * n := by
    intro n hn v hv
    rw [← P.inf_centralizer_eq hA] at hn
    exact (Subgroup.mem_centralizer_iff.mp hn.2 v hv).symm
  have hidx : ((Qv α ⊓ Qv β).subgroupOf (Qv α)).index = 2 := P.relIndex_inf_left hA h28
  have hz'Q : g * z * g⁻¹ ∈ Qv α :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab α) hg) z).mp hz
  have hn : z⁻¹ * (g * z * g⁻¹) ∈ Qv α ⊓ Qv β := by
    have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨z⁻¹, inv_mem hz⟩)
      (b := ⟨g * z * g⁻¹, hz'Q⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at h
    refine h.mpr ?_
    rw [inv_mem_iff]
    exact Subgroup.mem_normalizer_iff.mp (P.normalizer_inf hA hg) z
  set n := z⁻¹ * (g * z * g⁻¹) with hndef
  set a := g * y * g⁻¹ * y⁻¹ with hadef
  have ha : a ∈ Zv α := hcZ g hg y hyY
  have hzg : g * z * g⁻¹ = z * n := by rw [hndef]; group
  have hyg : g * y * g⁻¹ = a * y := by rw [hadef]; group
  have hay : a * y ∈ Zv α ⊔ Zv β := Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) hyY
  have hn_ay : n * (a * y) = (a * y) * n := hNY n hn _ hay
  have hza : z * a = a * z := hZc a ha z hz
  have hcz : z * y * z⁻¹ * y⁻¹ ∈ Zv α := hcZ z hzs y hyY
  have hcza : (z * y * z⁻¹ * y⁻¹) * a = a * (z * y * z⁻¹ * y⁻¹) :=
    (hZc _ hcz a (Zv_le_Qv hA α ha)).symm
  calc g * (z * y * z⁻¹ * y⁻¹) * g⁻¹
      = (g * z * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
    _ = (z * n) * (a * y) * (z * n)⁻¹ * (a * y)⁻¹ := by rw [hzg, hyg]
    _ = z * (n * (a * y)) * n⁻¹ * z⁻¹ * (a * y)⁻¹ := by group
    _ = z * ((a * y) * n) * n⁻¹ * z⁻¹ * (a * y)⁻¹ := by rw [hn_ay]
    _ = (z * a) * y * z⁻¹ * y⁻¹ * a⁻¹ := by group
    _ = a * z * y * z⁻¹ * y⁻¹ * a⁻¹ := by rw [hza]
    _ = (a * (z * y * z⁻¹ * y⁻¹)) * a⁻¹ := by group
    _ = ((z * y * z⁻¹ * y⁻¹) * a) * a⁻¹ := by rw [hcza]
    _ = z * y * z⁻¹ * y⁻¹ := by group

theorem exists_comm_ne_one (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β) :
    ∃ q ∈ Qv α, ∃ y ∈ Zv β, q * y * q⁻¹ * y⁻¹ ≠ 1 := by
  have hidx := P.relIndex_inf_left hA h28
  have hQN : ¬ Qv α ≤ Qv α ⊓ Qv β := fun h => by
    rw [Subgroup.relIndex_eq_one.mpr h] at hidx
    omega
  obtain ⟨q, hq, hqN⟩ := Set.not_subset.mp hQN
  refine ⟨q, hq, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hqN
  rw [← P.inf_centralizer_eq hA]
  refine ⟨pCoreOf_le 2 _ hq, ?_⟩
  have hle : Zv α ⊔ Zv β ≤ Subgroup.centralizer ({q} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α ha).2 q hq).symm
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc b * q = (q * b * q⁻¹ * b⁻¹)⁻¹ * (q * b) := by group
        _ = q * b := by rw [hcon b hb, inv_one, one_mul]
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

theorem mem_oTwoRes_sup (hA : F53Amalgam H M S) (P : Sit27 α β)
    (htop : Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
      Set ↥(stab α)) = ⊤) :
    ∀ g ∈ stab α, g ∈ oTwoRes (stab α) ⊔ Qv β := by
  set K := oTwoRes (stab α) ⊔ Qv β with hK
  have hconjR : ∀ g ∈ stab α, ∀ a ∈ oTwoRes (stab α), g * a * g⁻¹ ∈ oTwoRes (stab α) :=
    fun g hg a ha => (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes _ hg) a).mp ha
  have hQβs : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA P.nbr'
  have hR : oTwoRes (stab α) ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ r ∈ oTwoRes (stab α), ∀ v ∈ K, r * v * r⁻¹ ∈ K := fun r hr =>
      conj_mem_sup (fun a ha => Subgroup.mem_sup_left
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr ha) (Subgroup.inv_mem _ hr)))
        (fun d hd => by
          have h1 : d * r⁻¹ * d⁻¹ ∈ oTwoRes (stab α) :=
            hconjR d (hQβs hd) _ (Subgroup.inv_mem _ hr)
          have e : r * d * r⁻¹ = (r * (d * r⁻¹ * d⁻¹)) * d := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ hr h1))
            (Subgroup.mem_sup_right hd))
    intro r hr
    exact mem_normalizer_of_conj_le (key r hr) (key r⁻¹ (Subgroup.inv_mem _ hr))
  have hS : stab α ⊓ stab β ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ s ∈ stab α ⊓ stab β, ∀ v ∈ K, s * v * s⁻¹ ∈ K := fun s hs =>
      conj_mem_sup (fun a ha => Subgroup.mem_sup_left (hconjR s hs.1 a ha))
        (fun d hd => Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab β) hs.2) d).mp hd))
    intro s hs
    exact mem_normalizer_of_conj_le (key s hs) (key s⁻¹ (Subgroup.inv_mem _ hs))
  have hKn : stab α ≤ Subgroup.normalizer (K : Set G) :=
    (le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hA P.nbr)).trans (sup_le hR hS)
  have hKN : (K.subgroupOf (stab α)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hKn g.2) n).mp hn⟩
  have hBK : (Qv β).subgroupOf (stab α) ≤ K.subgroupOf (stab α) := fun d hd =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hd))
  have hLK := Subgroup.normalClosure_le_normal (N := K.subgroupOf (stab α)) (fun x hx => hBK hx)
  intro g hg
  have hgK : (⟨g, hg⟩ : ↥(stab α)) ∈ K.subgroupOf (stab α) :=
    hLK (by rw [htop]; exact Subgroup.mem_top _)
  exact Subgroup.mem_subgroupOf.mp hgK

theorem sq_mem_Qv (hA : F53Amalgam H M S) (P : Sit27 α β) {o : G}
    (ho : o ∈ oTwoRes (stab α)) (hoS : o ∈ stab α ⊓ stab β) : o ^ 2 ∈ Qv α := by
  obtain ⟨ψ, hψ, hψk⟩ := exists_quotHom_five (quot_stab_five hA P.vα)
  replace hψk : ψ.ker = (Qv α).subgroupOf (stab α) := hψk
  have hos : o ∈ stab α := oTwoRes_le _ ho
  have hsign := sign_eq_one_of_mem_oTwoRes ψ ho
  set T : Subgroup (Perm (Fin 5)) := ((stab α ⊓ stab β).subgroupOf (stab α)).map ψ with hTdef
  have hT : Nat.card T = 8 := by
    rw [hTdef, ← relIndex_inf_eq_card_map hψk inf_le_left,
      inf_eq_right.mpr (Qv_le_inf hA P.nbr)]
    exact relIndex_Qv_inf_false hA P.nbr P.vα
  have hoT : ψ ⟨o, hos⟩ ∈ T := ⟨⟨o, hos⟩, Subgroup.mem_subgroupOf.mpr hoS, rfl⟩
  have h8 : ψ ⟨o, hos⟩ ^ 8 = 1 := by
    have := pow_card_eq_one' (G := T) (x := ⟨_, hoT⟩)
    rw [hT] at this
    exact congrArg Subtype.val this
  have h2 := perm5_sq_eq_one_of_sign_of_pow_eight _ hsign h8
  have hk : (⟨o, hos⟩ : ↥(stab α)) ^ 2 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, h2]
  rw [hψk, Subgroup.mem_subgroupOf] at hk
  simpa using hk

theorem false_of_normalClosure_eq_top (hA : F53Amalgam H M S) (h28 : Hss28At H M)
    (h113c : Hss113cAt H M) (hlift : SecLiftFix) (P : Sit27 α β)
    (htop : Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
      Set ↥(stab α)) = ⊤) : False := by
  obtain ⟨α', hc⟩ := exists_critData hA P.bα P.adj
  have hz : ⁅Zv α, Zv α'⁆ ≠ ⊥ := fun hz => P.ncen (Zv_central_of_comm_eq_bot hA hc hz)
  have hmod := h113c α α' ⟨hc.not_le, hc.dist_eq⟩ hz P.vα
  set C₀ := Zv α ⊓ Subgroup.centralizer (oTwoRes (stab α) : Set G) with hC₀
  have hC₀n : stab α ≤ Subgroup.normalizer (C₀ : Set G) :=
    le_normalizer_inf (stab_le_normalizer_Zv hA α)
      ((le_normalizer_oTwoRes (stab α)).trans (normalizer_le_normalizer_centralizer _))
  have hC₀R : ∀ r ∈ oTwoRes (stab α), ∀ x ∈ C₀, r * x = x * r := fun r hr x hx =>
    Subgroup.mem_centralizer_iff.mp hx.2 r hr
  have hZc : ∀ a ∈ Zv α, ∀ v ∈ Qv α, v * a = a * v := fun a ha v hv =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α ha).2 v hv
  obtain ⟨q, hq, y, hy, hu⟩ := P.exists_comm_ne_one hA h28
  have hyQ : y ∈ Qv α := P.Zv_right_le_Qv hy
  have hcZ := P.conj_comm_mem_Zv hA htop
  set c : G → G := fun g => g * y * g⁻¹ * y⁻¹ with hcdef
  have hcA : ∀ g ∈ stab α, c g ∈ Zv α := fun g hg => hcZ g hg y (Subgroup.mem_sup_right hy)
  have hcoc : ∀ g h : G, c (g * h) = g * c h * g⁻¹ * c g := fun g h => by
    simp only [c]; group
  have hcQ : ∀ z ∈ Qv α, c z ∈ C₀ := fun z hz => ⟨hcA z (pCoreOf_le 2 _ hz),
    Subgroup.mem_centralizer_iff.mpr fun r hr => by
      have h := P.conj_comm_Qv_eq hA h28 htop hz hy r (oTwoRes_le _ hr)
      calc r * c z = (r * c z * r⁻¹) * r := by group
        _ = c z * r := by rw [h]⟩
  have hcβ : ∀ d ∈ Qv β, c d = 1 := fun d hd => by
    have h : d * y = y * d := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hy).2 d hd
    simp only [c, h]; group
  have hq28 := h28 (by have := P.b2; omega) α β P.adj P.bα
  have hβnα : Qv β ≤ Subgroup.normalizer (Qv α : Set G) :=
    (Qv_le_stab_of_mem_nbrs hA P.nbr').trans (le_normalizer_pCoreOf 2 (stab α))
  have hcS : ∀ s ∈ stab α ⊓ stab β, c s ∈ C₀ := by
    intro s hs
    rw [← hq28] at hs
    obtain ⟨z, hz, d, hd, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hβnα).mp hs
    rw [hcoc, hcβ d hd, mul_one, mul_inv_cancel, one_mul]
    exact hcQ z hz
  have hSyl := sylow_stab_inf_left hA P.nbr
  obtain ⟨w, hw, hwc⟩ := exists_mem_cocycle_mul_inv_mem hSyl.1 hSyl.2.2 (isElemAbelian_Zv hA α)
    (stab_le_normalizer_Zv hA α) inf_le_left hC₀n c hcA (fun g _ h _ => hcoc g h) hcS
  have hc'C : ∀ g ∈ stab α, g * (y * w⁻¹) * g⁻¹ * (y * w⁻¹)⁻¹ ∈ C₀ := by
    intro g hg
    have hb : g * w⁻¹ * g⁻¹ ∈ Zv α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) _).mp (inv_mem hw)
    have h1 : g * w⁻¹ * g⁻¹ * w = w * (g * w⁻¹ * g⁻¹) := (hZc _ hb w (Zv_le_Qv hA α hw)).symm
    have hwb : w * (g * w⁻¹ * g⁻¹) ∈ Zv α := mul_mem hw hb
    have h2 : (w * (g * w⁻¹ * g⁻¹)) * y⁻¹ = y⁻¹ * (w * (g * w⁻¹ * g⁻¹)) :=
      (hZc _ hwb y⁻¹ (inv_mem hyQ)).symm
    have e : g * (y * w⁻¹) * g⁻¹ * (y * w⁻¹)⁻¹ = c g * (g * w * g⁻¹ * w⁻¹)⁻¹ := by
      calc g * (y * w⁻¹) * g⁻¹ * (y * w⁻¹)⁻¹
          = (g * y * g⁻¹) * ((g * w⁻¹ * g⁻¹) * w) * y⁻¹ := by group
        _ = (g * y * g⁻¹) * ((w * (g * w⁻¹ * g⁻¹)) * y⁻¹) := by rw [h1]; group
        _ = (g * y * g⁻¹) * (y⁻¹ * (w * (g * w⁻¹ * g⁻¹))) := by rw [h2]
        _ = c g * (g * w * g⁻¹ * w⁻¹)⁻¹ := by simp only [c]; group
    rw [e]
    exact hwc g hg
  have hRy : ∀ r ∈ oTwoRes (stab α), r * (y * w⁻¹) = (y * w⁻¹) * r := by
    have hle : oTwoRes (stab α) ≤ Subgroup.centralizer ({y * w⁻¹} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hx, m, hm, hxm⟩
      have hxR : x ∈ oTwoRes (stab α) := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_odd_of_conj_mem (C := C₀) (fun c hc => (isElemAbelian_Zv hA α).2 c hc.1) hm
          hxm (hC₀R x hxR) (fun k => hc'C _ (pow_mem hx k)))
    exact fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hle hr)
  have hqK := P.mem_oTwoRes_sup hA htop q (pCoreOf_le 2 _ hq)
  have hβnR : Qv β ≤ Subgroup.normalizer (oTwoRes (stab α) : Set G) :=
    (Qv_le_stab_of_mem_nbrs hA P.nbr').trans (le_normalizer_oTwoRes _)
  obtain ⟨o, ho, d, hd, hqod⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hβnR).mp hqK
  have hQβS : Qv β ≤ stab α ⊓ stab β := by
    have h := Qv_le_inf hA P.nbr'
    rwa [inf_comm] at h
  have hoS : o ∈ stab α ⊓ stab β := by
    have e : o = q * d⁻¹ := by rw [hqod]; group
    rw [e]
    exact mul_mem (Qv_le_inf hA P.nbr hq) (inv_mem (hQβS hd))
  have hoi : o⁻¹ ∈ oTwoRes (stab α) := inv_mem ho
  have hoiS : o⁻¹ ∈ stab α ⊓ stab β := inv_mem hoS
  have hsq : o⁻¹ ^ 2 ∈ pCoreOf 2 (stab α) := P.sq_mem_Qv hA hoi hoiS
  have hC₀o : C₀ ≤ Subgroup.centralizer ({o⁻¹} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hC₀R _ hoi x hx).symm
  have hwo : o⁻¹ * w * o⁻¹⁻¹ * w⁻¹ ∈ C₀ := by
    have h := mul_mem (inv_mem (hcS o⁻¹ hoiS)) (hwc o⁻¹ hoiS.1)
    rw [inv_mul_cancel_left] at h
    exact inv_mem_iff.mp h
  have hfix := hlift G (stab α) (Zv α) C₀ (quot_stab_five hA P.vα)
    (stab_le_normalizer_Zv hA α) (isElemAbelian_Zv hA α) (Qv_le_centralizer_Zv hA α)
    inf_le_left hmod o⁻¹ hoi hsq hC₀o w hw hwo
  have how : o⁻¹ * w = w * o⁻¹ := by
    calc o⁻¹ * w = (o⁻¹ * w * o⁻¹⁻¹) * o⁻¹ := by group
      _ = w * o⁻¹ := by rw [hfix]
  have hqw : q * w = w * q := hZc w hw q hq
  have hdw : d * w = w * d := by
    have e : d = o⁻¹ * q := by rw [hqod]; group
    rw [e, mul_assoc, hqw, ← mul_assoc, how, mul_assoc]
  have hdy : d * y = y * d := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hy).2 d hd
  have hdwi : d * w⁻¹ = w⁻¹ * d := by
    calc d * w⁻¹ = w⁻¹ * (w * d) * w⁻¹ := by group
      _ = w⁻¹ * (d * w) * w⁻¹ := by rw [hdw]
      _ = w⁻¹ * d := by group
  have hdy' : d * (y * w⁻¹) = (y * w⁻¹) * d := by
    rw [← mul_assoc, hdy, mul_assoc, hdwi, ← mul_assoc]
  have hqy' : q * (y * w⁻¹) = (y * w⁻¹) * q := by
    rw [hqod, mul_assoc, hdy', ← mul_assoc, hRy o ho, mul_assoc]
  have hqwi : q * w⁻¹ * q⁻¹ = w⁻¹ := by
    rw [hZc w⁻¹ (inv_mem hw) q hq, mul_inv_cancel_right]
  apply hu
  calc q * y * q⁻¹ * y⁻¹ = (q * y * q⁻¹) * (q * w⁻¹ * q⁻¹) * w * y⁻¹ := by rw [hqwi]; group
    _ = (q * (y * w⁻¹)) * q⁻¹ * (y * w⁻¹)⁻¹ := by group
    _ = 1 := by rw [hqy']; group

end Sit27

theorem hss27S5At_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h28 : Hss28At H M)
    (h113c : Hss113cAt H M) (hlift : SecLiftFix) : Hss27S5At H M := by
  intro hb α β hαβ hv hα hY
  by_contra hn
  have P : Sit27 α β := ⟨hαβ, hv, hα, hb, hY, hn⟩
  rcases P.normalClosure_eq_top_or hA h28 with htop | hle
  · exact P.false_of_normalClosure_eq_top hA h28 h113c hlift htop
  · exact P.false_of_inf_le hA h26 h28 hle

end F53.Stellmacher

end CFSG.Quasithin
