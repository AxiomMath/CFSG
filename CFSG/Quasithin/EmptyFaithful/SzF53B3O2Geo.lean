module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3OrthDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O2Mod
public import CFSG.Quasithin.EmptyFaithful.SzF53B3A4

public section

namespace CFSG.Quasithin.F53Mod.O2

open Equiv CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem OrthDatum.ker_eq {F L X S₀ U : Subgroup G} (D : OrthDatum F L X S₀ U) :
    D.Ψ.ker = (pCoreOf 2 F).subgroupOf F := by
  ext a
  rw [MonoidHom.mem_ker, D.ker a, Subgroup.mem_subgroupOf]

theorem OrthDatum.comm_iff {F L X S₀ U : Subgroup G} (D : OrthDatum F L X S₀ U) (a b : ↥F) :
    D.Ψ a * D.Ψ b = D.Ψ b * D.Ψ a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 F := by
  have h : D.Ψ (a * b * a⁻¹ * b⁻¹) = D.Ψ a * D.Ψ b * (D.Ψ a)⁻¹ * (D.Ψ b)⁻¹ := by
    simp [map_mul, map_inv]
  rw [← comm_eq_one_iff, ← h, D.ker]
  exact Iff.rfl

end CFSG.Quasithin.F53Mod.O2

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53Mod.O2 CFSG.Quasithin.CosetGeom

namespace F53B3

namespace O2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Zv_le_Zv_mu (hBl : B3Block H M S) {μ w : Geo H M} (hμ : vtype μ = true)
    (hw : w ∈ nbrs μ) : Zv w ≤ Zv μ :=
  hBl.zv_le_zv w μ (vtype_nbr_of_true hw hμ)
    (show (graph (H ⊔ M) H M).Adj w μ from (show (graph (H ⊔ M) H M).Adj μ w from hw).symm)

omit [Finite G] in
theorem Zv_mu_le_Vn {μ w : Geo H M} (hw : w ∈ nbrs μ) : Zv μ ≤ Vn w :=
  N37.Zv_le_Vn_of_adj
    (show (graph (H ⊔ M) H M).Adj w μ from (show (graph (H ⊔ M) H M).Adj μ w from hw).symm)

omit [Finite G] in
theorem Zv_le_inf (hBl : B3Block H M S) {μ x y w : Geo H M} (hμ : vtype μ = true)
    (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) (hw : w ∈ nbrs μ) : Zv w ≤ Vn x ⊓ Vn y :=
  le_inf ((Zv_le_Zv_mu hBl hμ hw).trans (Zv_mu_le_Vn hx))
    ((Zv_le_Zv_mu hBl hμ hw).trans (Zv_mu_le_Vn hy))

omit [Finite G] in
theorem Vn_le_Qv_mu (hBl : B3Block H M S) {μ w : Geo H M} (hw : w ∈ nbrs μ) : Vn w ≤ Qv μ :=
  hBl.vn_le_qv w μ (N37.dist_le_one_of_adj
    (show (graph (H ⊔ M) H M).Adj w μ from (show (graph (H ⊔ M) H M).Adj μ w from hw).symm))

theorem inf_le_Vn_third (hB : B3Base H M S) (hBl : B3Block H M S) {μ x y z : Geo H M}
    (hμ : vtype μ = true) (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) (hz : z ∈ nbrs μ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Vn x ⊓ Vn y ≤ Vn z := by
  obtain ⟨t, ht, hty⟩ := exists_swap hB.amalgam hμ hxy hxz hyz hx hy hz
  have hRn := hBl.vn_inf_normal y μ x hxy.symm hμ hx hy
  intro r hr
  have hr' : (t : G)⁻¹ * r * (t : G) ∈ Vn x ⊓ Vn y :=
    (Subgroup.mem_normalizer_iff''.mp (hRn ht.1) r).mp hr
  have h1 : r ∈ Vn (t • y) := by
    rw [Vn_smul]
    have := mul_mem_conjSub (g := (t : G)) hr'.2
    simpa [mul_assoc] using this
  rwa [hty] at h1

theorem card_Vn (hB : B3FactsO H M S) (hBl : B3Block H M S) (hC1 : OrthC1 H M S) {μ w : Geo H M}
    (hμ : vtype μ = true) (hw : w ∈ nbrs μ) : Nat.card (Vn w) = 32 := by
  have hwf := vtype_nbr_of_true hw hμ
  have hsec : IsOrthSec (stab w) (Zv w) (Vn w) := by
    have := hB.orth w hwf
    rwa [hC1.cv_eq w hwf] at this
  have h16 := hsec.relIndex_eq
  have hle : Zv w ≤ Vn w := (Zv_le_Zv_mu hBl hμ hw).trans (Zv_mu_le_Vn hw)
  have h := Subgroup.relIndex_mul_card (Zv w) (Vn w)
  rw [inf_of_le_left hle, h16, hB.card_two w hwf] at h
  omega

omit [Finite G] in
theorem mul_inv_mem_of_relIndex_two {K L : Subgroup G} (h2 : L.relIndex K = 2) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (haL : a ∉ L) (hbL : b ∉ L) : a * b⁻¹ ∈ L := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) h2 (a := ⟨a, ha⟩)
    (b := ⟨b⁻¹, K.inv_mem hb⟩)
  have h3 : (⟨a, ha⟩ * ⟨b⁻¹, K.inv_mem hb⟩ : ↥K) ∈ L.subgroupOf K := by
    rw [h]
    simp only [Subgroup.mem_subgroupOf, Subgroup.inv_mem_iff]
    exact ⟨fun h' => absurd h' haL, fun h' => absurd h' hbL⟩
  exact Subgroup.mem_subgroupOf.mp h3

omit [Finite G] in
theorem relIndex_Zv_R (hBl : B3Block H M S) {μ : Geo H M} (hμ : vtype μ = true)
    {R : Subgroup G} (hZR : Zv μ ≤ R) (hR8 : Nat.card R = 8) : (Zv μ).relIndex R = 2 := by
  have h := Subgroup.relIndex_mul_card (Zv μ) R
  rw [inf_of_le_left hZR, hBl.card_zv_s3 μ hμ, hR8] at h
  omega

omit [Finite G] in
theorem exists_not_mem_Zv (hBl : B3Block H M S) {μ : Geo H M} (hμ : vtype μ = true)
    {R : Subgroup G} (hR8 : Nat.card R = 8) : ∃ r ∈ R, r ∉ Zv μ := by
  by_contra hcon
  push Not at hcon
  have h := Subgroup.card_dvd_of_le (show R ≤ Zv μ from hcon)
  rw [hR8, hBl.card_zv_s3 μ hμ] at h
  exact absurd h (by decide)

theorem comm_mem_Zv (hB : B3Base H M S) (hBl : B3Block H M S) {μ : Geo H M}
    (hμ : vtype μ = true) {R : Subgroup G} (hZR : Zv μ ≤ R) (hR8 : Nat.card R = 8)
    (hRn : stab μ ≤ Subgroup.normalizer (R : Set G)) {q r : G} (hq : q ∈ Qv μ) (hr : r ∈ R) :
    q * r * q⁻¹ * r⁻¹ ∈ Zv μ :=
  comm_mem_of_card hZR (by rw [hR8, hBl.card_zv_s3 μ hμ])
    (stab_le_normalizer_Zv hB.amalgam μ (N37.Qv_le_stab_self μ hq))
    (hRn (N37.Qv_le_stab_self μ hq)) hr

theorem comm_eq_of_not_mem (hB : B3Base H M S) (hBl : B3Block H M S) {μ : Geo H M}
    (hμ : vtype μ = true) {R : Subgroup G} (hZR : Zv μ ≤ R) (hR8 : Nat.card R = 8)
    (hRn : stab μ ≤ Subgroup.normalizer (R : Set G)) {q r₀ r : G} (hq : q ∈ Qv μ) (hr₀ : r₀ ∈ R)
    (hr₀Z : r₀ ∉ Zv μ) (hr : r ∈ R) (hrZ : r ∉ Zv μ) :
    q * r * q⁻¹ * r⁻¹ = q * r₀ * q⁻¹ * r₀⁻¹ := by
  have hz := mul_inv_mem_of_relIndex_two (relIndex_Zv_R hBl hμ hZR hR8) hr hr₀ hrZ hr₀Z
  obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ Zv μ, r = z' * r₀ := ⟨r * r₀⁻¹, hz, by group⟩
  have hqz : z' * q = q * z' :=
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hB.amalgam μ hq) z' hz'
  have ht := comm_mem_Zv hB hBl hμ hZR hR8 hRn hq hr₀
  have hzt : z' * (q * r₀ * q⁻¹ * r₀⁻¹) = (q * r₀ * q⁻¹ * r₀⁻¹) * z' :=
    mul_comm_of_elemAbelian (isElemAbelian_Zv hB.amalgam μ) hz' ht
  calc q * (z' * r₀) * q⁻¹ * (z' * r₀)⁻¹
      = (q * z' * q⁻¹) * (q * r₀ * q⁻¹ * r₀⁻¹) * z'⁻¹ := by group
    _ = z' * (q * r₀ * q⁻¹ * r₀⁻¹) * z'⁻¹ := by rw [← hqz]; group
    _ = q * r₀ * q⁻¹ * r₀⁻¹ := by rw [hzt]; group

theorem Zv_inf_Zv (hB : B3Base H M S) {μ x y : Geo H M} (hμ : vtype μ = true) (hxy : x ≠ y)
    (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) {t : G} (htx : t ∈ Zv x) (hty : t ∈ Zv y) : t = 1 := by
  obtain ⟨a, haZ, ha1, hau⟩ := exists_gen_of_card_two (hB.card_two x (vtype_nbr_of_true hx hμ))
  obtain ⟨b, hbZ, hb1, hbu⟩ := exists_gen_of_card_two (hB.card_two y (vtype_nbr_of_true hy hμ))
  have hab := ne_of_gen_ne hbZ haZ hau hbu (Zv_ne_of_ne hB hμ hxy hx hy)
  rcases hau t htx with h | h
  · exact h
  · rcases hbu t hty with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hab

theorem Zv_subset_union (hB : B3Base H M S) (hBl : B3Block H M S) {μ x y z : Geo H M}
    (hμ : vtype μ = true) (hx : x ∈ nbrs μ) (hy : y ∈ nbrs μ) (hz : z ∈ nbrs μ) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : ∀ t ∈ Zv μ, t ∈ Zv x ∨ t ∈ Zv y ∨ t ∈ Zv z := by
  have hxf := vtype_nbr_of_true hx hμ
  have hyf := vtype_nbr_of_true hy hμ
  have hzf := vtype_nbr_of_true hz hμ
  obtain ⟨a, haZ, ha1, hau⟩ := exists_gen_of_card_two (hB.card_two x hxf)
  obtain ⟨b, hbZ, hb1, hbu⟩ := exists_gen_of_card_two (hB.card_two y hyf)
  obtain ⟨c, hcZ, hc1, hcu⟩ := exists_gen_of_card_two (hB.card_two z hzf)
  have hab := ne_of_gen_ne hbZ haZ hau hbu (Zv_ne_of_ne hB hμ hxy hx hy)
  have hac := ne_of_gen_ne hcZ haZ hau hcu (Zv_ne_of_ne hB hμ hxz hx hz)
  have hbc := ne_of_gen_ne hcZ hbZ hbu hcu (Zv_ne_of_ne hB hμ hyz hy hz)
  have hxμ := Zv_le_Zv_mu hBl hμ hx
  have hidx : (Zv x).relIndex (Zv μ) = 2 := by
    have h := Subgroup.relIndex_mul_card (Zv x) (Zv μ)
    rw [inf_of_le_left hxμ, hB.card_two x hxf, hBl.card_zv_s3 μ hμ] at h
    omega
  have hbx : b ∉ Zv x := fun h => (hau b h).elim hb1 fun h' => hab h'.symm
  have hcx : c ∉ Zv x := fun h => (hau c h).elim hc1 fun h' => hac h'.symm
  intro t htμ
  by_cases htx : t ∈ Zv x
  · exact Or.inl htx
  · have h1 := mul_inv_mem_of_relIndex_two hidx htμ (Zv_le_Zv_mu hBl hμ hy hbZ) htx hbx
    have h2 := mul_inv_mem_of_relIndex_two hidx (Zv_le_Zv_mu hBl hμ hz hcZ)
      (Zv_le_Zv_mu hBl hμ hy hbZ) hcx hbx
    rcases hau _ h1 with h1' | h1'
    · refine Or.inr (Or.inl ?_)
      rw [mul_inv_eq_one.mp h1']
      exact hbZ
    · rcases hau _ h2 with h2' | h2'
      · exact absurd (mul_inv_eq_one.mp h2') hbc.symm
      · refine Or.inr (Or.inr ?_)
        have : t = c := by
          have e : t * b⁻¹ = c * b⁻¹ := h1'.trans h2'.symm
          exact mul_right_cancel e
        rw [this]
        exact hcZ

theorem local_datum (hB : B3FactsO H M S) (hC1 : OrthC1 H M S) {μ w : Geo H M}
    (hμ : vtype μ = true) (hw : w ∈ nbrs μ) {R : Subgroup G} (hZR : Zv w ≤ R) (hRV : R ≤ Vn w)
    (hRn : stab μ ≤ Subgroup.normalizer (R : Set G)) (hR8 : Nat.card R = 8) :
    Nonempty (OrthDatum (stab w) (Zv w) (Vn w) (stab μ ⊓ stab w) R) := by
  have hwf := vtype_nbr_of_true hw hμ
  have hsec : IsOrthSec (stab w) (Zv w) (Vn w) := by
    have := hB.orth w hwf
    rwa [hC1.cv_eq w hwf] at this
  have hS : IsSylowTwoOf (stab μ ⊓ stab w) (stab w) :=
    N37.sylow_inf_stab hB.amalgam
      (show (graph (H ⊔ M) H M).Adj w μ from (show (graph (H ⊔ M) H M).Adj μ w from hw).symm)
  have h4 : (Zv w).relIndex R = 4 := by
    have h := Subgroup.relIndex_mul_card (Zv w) R
    rw [inf_of_le_left hZR, hB.card_two w hwf, hR8] at h
    omega
  exact exists_orthDatum hsec (quot_stab_five hB.amalgam hwf) hS hZR hRV (inf_le_left.trans hRn)
    h4

theorem map_Qv_mu_eq (hB : B3Base H M S) {μ w : Geo H M} (hμ : vtype μ = true)
    (hw : w ∈ nbrs μ) {L X U : Subgroup G} (D : OrthDatum (stab w) L X (stab μ ⊓ stab w) U) :
    ((Qv μ).subgroupOf (stab w)).map D.Ψ = S5Syl := by
  have hprod : Qv μ ⊔ Qv w = stab μ ⊓ stab w := hB.prod μ w hw hμ
  have h1 : Qv μ ≤ stab w := Qv_le_stab_of_mem_nbrs hB.amalgam hw
  have h2 : Qv w ≤ stab w := N37.Qv_le_stab_self w
  have hbot : ((Qv w).subgroupOf (stab w)).map D.Ψ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [D.ker_eq]; exact le_rfl)
  have key : ∀ T : Subgroup G, T = stab μ ⊓ stab w → (T.subgroupOf (stab w)).map D.Ψ = S5Syl := by
    intro T hT
    rw [hT]
    exact D.map_syl
  have h := key (Qv μ ⊔ Qv w) hprod
  rw [Subgroup.subgroupOf_sup h1 h2, Subgroup.map_sup, hbot, sup_bot_eq] at h
  exact h

theorem Ψ_mem_S5Syl (hB : B3Base H M S) {μ w : Geo H M} (hμ : vtype μ = true) (hw : w ∈ nbrs μ)
    {L X U : Subgroup G} (D : OrthDatum (stab w) L X (stab μ ⊓ stab w) U) {q : ↥(stab w)}
    (hq : (q : G) ∈ Qv μ) : D.Ψ q ∈ S5Syl := by
  rw [← map_Qv_mu_eq hB hμ hw D]
  exact ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩

theorem exists_Qmu_image (hB : B3Base H M S) {μ w : Geo H M} (hμ : vtype μ = true)
    (hw : w ∈ nbrs μ) {L X U : Subgroup G} (D : OrthDatum (stab w) L X (stab μ ⊓ stab w) U)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ S5Syl) : ∃ q : ↥(stab w), (q : G) ∈ Qv μ ∧ D.Ψ q = τ := by
  rw [← map_Qv_mu_eq hB hμ hw D] at hτ
  obtain ⟨q, hq, rfl⟩ := hτ
  exact ⟨q, Subgroup.mem_subgroupOf.mp hq, rfl⟩

theorem datum_iff_comm (hB : B3Base H M S) (hBl : B3Block H M S) {μ w : Geo H M}
    (hμ : vtype μ = true) {R : Subgroup G} (hZR : Zv μ ≤ R) (hR8 : Nat.card R = 8)
    (hRn : stab μ ≤ Subgroup.normalizer (R : Set G))
    (D : OrthDatum (stab w) (Zv w) (Vn w) (stab μ ⊓ stab w) R) {r₀ : G} (hr₀ : r₀ ∈ R)
    (hr₀Z : r₀ ∉ Zv μ) {q : ↥(stab w)} (hq : (q : G) ∈ Qv μ) :
    D.Ψ q ∈ S5That ↔ (q : G) * r₀ * (q : G)⁻¹ * r₀⁻¹ ∈ Zv w := by
  have hqS : (q : G) ∈ stab μ ⊓ stab w := ⟨N37.Qv_le_stab_self μ hq, q.2⟩
  rw [← D.kerU q hqS]
  constructor
  · intro h
    exact h r₀ hr₀
  · intro h u hu
    by_cases huZ : u ∈ Zv μ
    · have : (q : G) * u * (q : G)⁻¹ * u⁻¹ = 1 := by
        have hc := Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hB.amalgam μ hq) u huZ
        rw [mul_assoc, ← hc]
        group
      rw [this]
      exact (Zv w).one_mem
    · rw [comm_eq_of_not_mem hB hBl hμ hZR hR8 hRn hq hr₀ hr₀Z hu huZ]
      exact h

end O2

end F53B3

end CFSG.Quasithin
